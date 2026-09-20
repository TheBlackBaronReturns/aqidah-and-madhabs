#!/usr/bin/env python3
"""
Static analysis / lint checker for the Aqidah: Schools of Creed EU5 mod.

This is NOT a real Jomini-script parser - EU5 script has no public formal
grammar and this tool doesn't try to reconstruct one. Instead it targets
the SPECIFIC bug classes this mod's own source comments describe having
already cost real debugging hours (see e.g. z_aqd_jurist_triggers.txt's
header): an unreferenced $PARAM$ silently breaking the argument compiler,
a $PARAM$ substituted inside a quoted string silently evaluating empty,
and a typo'd identifier silently no-op'ing instead of erroring. All of
these fail SILENTLY in-game (no crash, no obvious symptom), which is
exactly what makes them worth catching before you spend an evening in
front of the game trying to figure out why a seat never got placed.

Checks, roughly in descending confidence:
  1.  Brace balance per file.
  2.  A $PARAM$ token substituted inside a quoted string ("...$X$...") -
      the documented always-empty-match gotcha.
  3.  A scripted_effect/scripted_trigger call site passes KEY=value but
      the definition body never references $KEY$ anywhere - the
      documented "unknown arguments" silent no-op.
  4.  An event's name/title/desc/custom_tooltip points at a localization
      key that doesn't exist in any English yml.
  5.  An aqd_*/z_aqd_* identifier is called (IDENT = yes / IDENT = { })
      but never defined anywhere in the mod - likely a typo, a stale
      call to something renamed/removed, or a load-order-dependent name.
  6.  building_type: / religious_school: / `modifier = X` references that
      resolve to neither a mod-defined nor a (best-effort, if found)
      vanilla-defined name.
  7.  A mod-defined effect/trigger/script_value/modifier that is never
      referenced anywhere else in the mod (dead code candidate).

Checks 5-7 are best-effort and will have some false positives (dynamic
name construction via text substitution - e.g. aqd_jurist_reaction_
$OUTCOME$_favored - can't be resolved statically, and are reported
separately, not as bugs). Checks 1-4 are close to zero-false-positive:
if this tool reports one of those, go look.

Usage:
    python tools/lint_mod.py [--vanilla PATH] [--no-vanilla] [--quiet]

Exit code is 1 if any Tier-1 (checks 1-4) issue was found, else 0 - so
this can be wired into a pre-commit hook or CI step later if wanted.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

MOD_ROOT = Path(__file__).resolve().parent.parent

# Candidate vanilla install locations to try if --vanilla isn't given.
VANILLA_CANDIDATES = [
    Path(r"C:\Program Files (x86)\Steam\steamapps\common\Europa Universalis V\game"),
    Path(r"C:\Program Files\Steam\steamapps\common\Europa Universalis V\game"),
]

# Structural / engine keywords that are never mod-defined identifiers,
# so they must never be flagged as "possibly undefined aqd_ identifier"
# (they wouldn't match the aqd_/z_aqd_ prefix filter anyway, but kept
# here as the single place that knowledge lives if that filter ever
# loosens).
STRUCTURAL_KEYWORDS = {
    "limit", "trigger", "effect", "if", "else_if", "else", "while",
    "OR", "AND", "NOT", "NOR", "option", "immediate", "after", "desc",
    "title", "name", "type", "outcome", "random", "random_list",
    "random_events", "on_actions", "trigger_event", "trigger_event_non_silently",
}

PARAM_TOKEN_RE = re.compile(r"\$([A-Za-z_][A-Za-z0-9_]*)\$")
QUOTED_STRING_RE = re.compile(r'"([^"\n]*)"')
TOPLEVEL_DEF_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*\{", re.MULTILINE)
EVENT_DEF_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*\.[0-9]+)\s*=\s*\{", re.MULTILINE)
CALL_BRACE_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*\{")
CALL_BOOL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(yes|no)\b")
KEY_EQ_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*=")
LOC_KEY_RE = re.compile(r'^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*:\s*\d*\s*"', re.MULTILINE)
LOC_FIELD_RE = re.compile(r"\b(name|title|desc|custom_tooltip)\s*=\s*([A-Za-z_][A-Za-z0-9_.]*)\b")
BUILDING_TYPE_REF_RE = re.compile(r"building_type:([A-Za-z0-9_$]+)")
RELIGIOUS_SCHOOL_REF_RE = re.compile(r"religious_school:([A-Za-z0-9_$]+)")
MODIFIER_FIELD_RE = re.compile(r"\bmodifier\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)")


# ---------------------------------------------------------------------
# Text utilities
# ---------------------------------------------------------------------

def strip_comments(text: str) -> str:
    """Blank out everything from an un-quoted '#' to end of line, in
    every line of `text`, preserving line/column positions (so
    line-number reporting on the ORIGINAL text stays correct if you
    index into this stripped copy)."""
    out = []
    for line in text.split("\n"):
        in_quotes = False
        cut = len(line)
        for i, ch in enumerate(line):
            if ch == '"':
                in_quotes = not in_quotes
            elif ch == "#" and not in_quotes:
                cut = i
                break
        out.append(line[:cut])
    return "\n".join(out)


def find_matching_brace(text: str, open_idx: int) -> int:
    """Given the index of an opening '{' in `text`, return the index of
    its matching '}', respecting quoted strings. Assumes text[open_idx]
    == '{'."""
    depth = 0
    in_quotes = False
    i = open_idx
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == '"':
            in_quotes = not in_quotes
        elif not in_quotes:
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return i
        i += 1
    return -1  # unbalanced - caller must handle


def extract_depth0_pairs(block_text: str) -> list[tuple[str, int, int]]:
    """Given the text strictly between a `{` and its matching `}`,
    return (KEY, value_start, key_start) for every `KEY = ...` that
    appears at depth 0 within this block (i.e. not inside a nested
    {...}) - the value itself is whatever follows up to the next
    depth-0 token, which callers re-match against their own value
    pattern starting at value_start."""
    pairs = []
    depth = 0
    in_quotes = False
    i = 0
    n = len(block_text)
    while i < n:
        ch = block_text[i]
        if ch == '"':
            in_quotes = not in_quotes
            i += 1
            continue
        if in_quotes:
            i += 1
            continue
        if ch == "{":
            depth += 1
            i += 1
            continue
        if ch == "}":
            depth -= 1
            i += 1
            continue
        if depth == 0:
            m = KEY_EQ_RE.match(block_text, i)
            if m:
                pairs.append((m.group(1), m.end(), m.start()))
                i = m.end()
                continue
        i += 1
    return pairs


def extract_depth0_keys(block_text: str) -> list[str]:
    return [k for k, _, _ in extract_depth0_pairs(block_text)]


def line_of(text: str, idx: int) -> int:
    return text.count("\n", 0, idx) + 1


def is_prefixed_reference(text: str, match_start: int) -> bool:
    """True if the identifier matched at `match_start` is actually the
    tail of a `scope:X` / `var:X` / `event_target:X` / `c:X` / `flag:X`
    style prefixed reference (a saved scope or variable re-entry), not a
    scripted_effect/trigger call - those look identical to a call
    (`NAME = { ... }` / `NAME = yes`) once you're only matching on the
    identifier itself, so callers must check the preceding character."""
    return match_start > 0 and text[match_start - 1] == ":"


# ---------------------------------------------------------------------
# Corpus
# ---------------------------------------------------------------------

@dataclass
class SourceFile:
    path: Path
    raw: str
    stripped: str  # comments blanked out, same length/line layout


@dataclass
class Definition:
    name: str
    file: Path
    line: int
    body: str  # text strictly between the matching braces
    start: int = -1  # char offset of the `NAME = {` match start, in that file's stripped text


@dataclass
class Corpus:
    script_files: list[SourceFile] = field(default_factory=list)
    loc_files: list[SourceFile] = field(default_factory=list)
    effects: dict[str, Definition] = field(default_factory=dict)
    triggers: dict[str, Definition] = field(default_factory=dict)
    script_values: dict[str, Definition] = field(default_factory=dict)
    modifiers: dict[str, Definition] = field(default_factory=dict)
    buildings: dict[str, Definition] = field(default_factory=dict)
    events: dict[str, Definition] = field(default_factory=dict)
    religious_schools: dict[str, Definition] = field(default_factory=dict)
    biases: dict[str, Definition] = field(default_factory=dict)  # opinion modifiers - a different
                                                                   # namespace from static_modifiers,
                                                                   # but both use a `modifier = X` field
    loc_keys: set[str] = field(default_factory=set)
    # Every top-level `NAME = { ... }` definition in ANY mod script file,
    # regardless of folder - covers categories check_undefined_aqd_calls
    # needs but the other, semantically-typed tables above don't track
    # (auto_modifiers, biases, generic_actions, generic_action_ai_lists,
    # laws, prices, production_methods, etc.). NOT used by the $PARAM$
    # check, which must stay scoped to true scripted_effects/triggers.
    all_names: dict[str, Definition] = field(default_factory=dict)


def load_script_files(root: Path) -> list[SourceFile]:
    files = []
    for p in sorted(root.rglob("*.txt")):
        if ".git" in p.parts:
            continue
        raw = p.read_text(encoding="utf-8-sig", errors="replace")
        files.append(SourceFile(p, raw, strip_comments(raw)))
    return files


def load_loc_files(root: Path) -> list[SourceFile]:
    files = []
    for p in sorted(root.rglob("*.yml")):
        if ".git" in p.parts:
            continue
        raw = p.read_text(encoding="utf-8-sig", errors="replace")
        files.append(SourceFile(p, raw, raw))  # no # comments to strip in loc yml
    return files


def scan_toplevel_defs(sf: SourceFile, pattern: re.Pattern) -> dict[str, Definition]:
    defs: dict[str, Definition] = {}
    for m in pattern.finditer(sf.stripped):
        # Only true top-level: no non-whitespace before this on its own
        # line other than the identifier itself (keeps us from matching
        # e.g. `save_scope_as = { ... }`-style nested constructs that
        # happen to start a line inside a deeply-indented block). We
        # approximate "top level of the FILE" by requiring depth 0 at
        # the match start, computed cheaply via brace count up to here.
        prefix = sf.stripped[: m.start()]
        # Fast depth check: count unmatched '{' before this point,
        # ignoring quotes.
        depth = 0
        in_q = False
        for ch in prefix:
            if ch == '"':
                in_q = not in_q
            elif not in_q:
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
        if depth != 0:
            continue
        name = m.group(1)
        open_idx = m.end() - 1
        close_idx = find_matching_brace(sf.stripped, open_idx)
        if close_idx == -1:
            continue
        body = sf.stripped[open_idx + 1 : close_idx]
        defs[name] = Definition(name, sf.path, line_of(sf.raw, m.start()), body, start=m.start())
    return defs


def build_corpus(root: Path) -> Corpus:
    c = Corpus()
    c.script_files = load_script_files(root)
    c.loc_files = load_loc_files(root / "main_menu" / "localization")

    for sf in c.script_files:
        c.all_names.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        c.all_names.update(scan_toplevel_defs(sf, EVENT_DEF_RE))

    for sf in c.script_files:
        rel = sf.path.relative_to(root).as_posix()
        if "/scripted_effects/" in rel:
            c.effects.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        elif "/scripted_triggers/" in rel:
            c.triggers.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        elif "/script_values/" in rel:
            c.script_values.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        elif "/static_modifiers/" in rel:
            c.modifiers.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        elif "/building_types/" in rel:
            c.buildings.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        elif "/religious_schools/" in rel:
            c.religious_schools.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        elif "/biases/" in rel:
            c.biases.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))
        if "/events/" in rel:
            c.events.update(scan_toplevel_defs(sf, EVENT_DEF_RE))

    for sf in c.loc_files:
        for m in LOC_KEY_RE.finditer(sf.raw):
            c.loc_keys.add(m.group(1))

    return c


# ---------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------

@dataclass
class Finding:
    tier: int
    check: str
    file: str
    line: int
    message: str


def check_brace_balance(files: list[SourceFile]) -> list[Finding]:
    out = []
    for sf in files:
        depth = 0
        in_q = False
        for ch in sf.stripped:
            if ch == '"':
                in_q = not in_q
            elif not in_q:
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
        if depth != 0:
            out.append(Finding(1, "brace-balance", str(sf.path), 1,
                                f"unbalanced braces (net {depth:+d}) - file will fail to parse"))
    return out


def check_quoted_param(files: list[SourceFile]) -> list[Finding]:
    out = []
    for sf in files:
        for qm in QUOTED_STRING_RE.finditer(sf.stripped):
            inner = qm.group(1)
            for pm in PARAM_TOKEN_RE.finditer(inner):
                ln = line_of(sf.raw, qm.start())
                out.append(Finding(
                    2, "quoted-param", str(sf.path), ln,
                    f'$${pm.group(1)}$$ substituted inside a quoted string '
                    f'("{inner}") - this ALWAYS evaluates with an empty '
                    f'value, silently, regardless of what the param is bound '
                    f'to. Use the structured block form instead.'
                ))
    return out


def check_param_mismatch(c: Corpus, files: list[SourceFile]) -> list[Finding]:
    out = []
    callable_defs: dict[str, Definition] = {**c.effects, **c.triggers}
    # Which $PARAM$s does each definition's body actually reference?
    defined_params: dict[str, set[str]] = {
        name: {m.group(1) for m in PARAM_TOKEN_RE.finditer(d.body)}
        for name, d in callable_defs.items()
    }
    # A definition's own `NAME = { ... }` line matches CALL_BRACE_RE too -
    # exclude those exact (file, offset) sites so a definition's own
    # top-level effects (if/set_variable/nested calls) are never
    # misread as "parameters passed to a call of itself".
    def_sites = {(str(d.file), d.start) for d in callable_defs.values()}
    for sf in files:
        for m in CALL_BRACE_RE.finditer(sf.stripped):
            name = m.group(1)
            if name not in callable_defs:
                continue
            if (str(sf.path), m.start()) in def_sites:
                continue
            if is_prefixed_reference(sf.stripped, m.start()):
                continue  # scope:X / var:X re-entry, not a call
            open_idx = m.end() - 1
            close_idx = find_matching_brace(sf.stripped, open_idx)
            if close_idx == -1:
                continue
            block = sf.stripped[open_idx + 1 : close_idx]
            passed_keys = set(extract_depth0_keys(block))
            missing = passed_keys - defined_params[name]
            if missing:
                ln = line_of(sf.raw, m.start())
                d = callable_defs[name]
                out.append(Finding(
                    3, "param-mismatch", str(sf.path), ln,
                    f"call to {name}() passes {sorted(missing)} but its "
                    f"definition ({d.file.name}:{d.line}) never references "
                    f"${{{list(missing)[0]}}}$ (or the equivalent) anywhere "
                    f"in its body - EU5's argument compiler will reject this "
                    f"call with 'unknown arguments', which silently no-ops "
                    f"the WHOLE call (nothing inside it runs)."
                ))
    return out


def _find_blocks(text: str, keyword: str) -> list[tuple[int, int]]:
    """Return (open_idx, close_idx) for every `keyword = { ... }` block
    anywhere in `text` (any nesting depth)."""
    spans = []
    for m in re.finditer(r"\b" + re.escape(keyword) + r"\s*=\s*\{", text):
        open_idx = m.end() - 1
        close_idx = find_matching_brace(text, open_idx)
        if close_idx != -1:
            spans.append((open_idx, close_idx))
    return spans


def check_missing_loc(c: Corpus, all_loc_keys: set[str], files: list[SourceFile]) -> list[Finding]:
    out = []
    seen: set[tuple[str, int, str]] = set()

    def _report(sf, field_name, key, idx):
        if key in ("yes", "no"):
            return
        if key in all_loc_keys:
            return
        ln = line_of(sf.raw, idx)
        sig = (str(sf.path), ln, key)
        if sig in seen:
            return
        seen.add(sig)
        out.append(Finding(
            4, "missing-loc", str(sf.path), ln,
            f'{field_name} = {key} has no matching localization key '
            f'in any English yml (mod or vanilla) - this will show the raw '
            f'key (or a MISSING_KEY placeholder) in-game instead of text.'
        ))

    for sf in files:
        if "/events/" not in sf.path.as_posix():
            continue
        text = sf.stripped
        # title / desc / custom_tooltip: safe to scan flat across the
        # whole event (this also catches nested triggered_desc.desc=KEY),
        # since none of those field names collide with an unrelated
        # non-loc-key usage anywhere else in this mod's script.
        for m in re.finditer(r"\b(title|desc|custom_tooltip)\s*=\s*([A-Za-z_][A-Za-z0-9_.]*)\b", text):
            _report(sf, m.group(1), m.group(2), m.start())
        # name: NOT safe to scan flat - `set_variable`/`change_variable`
        # also have a `name = <var_name>` field with a totally different
        # meaning (a variable name, never a loc key). A loc-referencing
        # `name =` only ever appears as an option's own field, so scope
        # the scan to option={...} blocks specifically.
        for open_idx, close_idx in _find_blocks(text, "option"):
            block = text[open_idx + 1 : close_idx]
            for key, value_start, key_start in extract_depth0_pairs(block):
                if key != "name":
                    continue
                vm = re.match(r"([A-Za-z_][A-Za-z0-9_.]*)\b", block[value_start:])
                if vm:
                    _report(sf, "name", vm.group(1), open_idx + 1 + key_start)
    return out


def check_undefined_aqd_calls(c: Corpus, files: list[SourceFile]) -> list[Finding]:
    out = []
    known = set(c.all_names) | STRUCTURAL_KEYWORDS
    seen: set[tuple[str, int, str]] = set()
    for sf in files:
        for pattern in (CALL_BRACE_RE, CALL_BOOL_RE):
            for m in pattern.finditer(sf.stripped):
                name = m.group(1)
                if not (name.startswith("aqd_") or name.startswith("z_aqd_")):
                    continue
                if name in known:
                    continue
                if "$" in name:
                    continue  # unresolved dynamic name, can't check statically
                if is_prefixed_reference(sf.stripped, m.start()):
                    continue  # scope:X / var:X re-entry, not a call
                ln = line_of(sf.raw, m.start())
                sig = (str(sf.path), ln, name)
                if sig in seen:
                    continue
                seen.add(sig)
                out.append(Finding(
                    5, "undefined-call", str(sf.path), ln,
                    f"'{name}' is called here but is not defined as a "
                    f"scripted_effect, scripted_trigger, or script_value "
                    f"anywhere in the mod - possible typo, stale reference "
                    f"to something renamed/removed, or a dynamically-"
                    f"constructed name this tool can't resolve (review before "
                    f"trusting this one)."
                ))
    return out


def check_reference_targets(c: Corpus, files: list[SourceFile],
                             vanilla: "Corpus | None") -> list[Finding]:
    out = []
    known_buildings = set(c.buildings) | (set(vanilla.buildings) if vanilla else set())
    known_schools = set(c.religious_schools) | (set(vanilla.religious_schools) if vanilla else set())
    known_modifiers = (set(c.modifiers) | set(c.biases)
                       | (set(vanilla.modifiers) | set(vanilla.biases) if vanilla else set()))
    seen: set[tuple[str, int, str, str]] = set()

    def _report(sf, m, kind, name, known_set, note):
        if name in known_set or "$" in name:
            return
        ln = line_of(sf.raw, m.start())
        sig = (str(sf.path), ln, kind, name)
        if sig in seen:
            return
        seen.add(sig)
        out.append(Finding(6, kind, str(sf.path), ln,
                            f"{kind}:{name} {note}"))

    for sf in files:
        for m in BUILDING_TYPE_REF_RE.finditer(sf.stripped):
            _report(sf, m, "building_type", m.group(1), known_buildings,
                     "does not resolve to a mod- or vanilla-defined building_type "
                     "(vanilla check skipped - game install not found)" if vanilla is None
                     else "does not resolve to a mod- or vanilla-defined building_type")
        for m in RELIGIOUS_SCHOOL_REF_RE.finditer(sf.stripped):
            _report(sf, m, "religious_school", m.group(1), known_schools,
                     "does not resolve to a mod- or vanilla-defined religious_school")
        for m in MODIFIER_FIELD_RE.finditer(sf.stripped):
            name = m.group(1)
            if name == "category":
                continue
            _report(sf, m, "modifier", name, known_modifiers,
                     "does not resolve to a mod- or vanilla-defined static modifier")
    return out


def _dynamic_reference_exists(name: str, whole_text: str) -> bool:
    """This mod builds many effect/trigger names by text substitution -
    aqd_crackdown_destroy_$MADHHAB$_madrasa, aqd_jurist_reaction_$OUTCOME$_
    favored, aqd_jurists_finish_$ENDOW$ - so a literal-substring reference
    count of 'aqd_crackdown_destroy_hanafi_madrasa' finds nothing even
    though it's very much called, just never by its literal name. Try
    replacing each underscore-delimited segment of `name` with a $WORD$-
    shaped wildcard and see if THAT pattern appears anywhere - if so, this
    is (almost certainly) a dynamically-dispatched name, not dead code."""
    parts = name.split("_")
    if len(parts) < 2:
        return False
    for i in range(len(parts)):
        pattern_parts = [re.escape(p) for p in parts]
        pattern_parts[i] = r"\$[A-Za-z_]+\$"
        pattern = "_".join(pattern_parts)
        if re.search(pattern, whole_text):
            return True
    return False


def check_unused_symbols(c: Corpus, files: list[SourceFile]) -> list[Finding]:
    out = []
    whole_text = "\n".join(sf.stripped for sf in files)
    tables = [
        ("scripted_effect", c.effects),
        ("scripted_trigger", c.triggers),
        ("script_value", c.script_values),
        ("static_modifier", c.modifiers),
    ]
    for kind, table in tables:
        for name, d in table.items():
            count = len(re.findall(r"\b" + re.escape(name) + r"\b", whole_text))
            if count <= 1 and not _dynamic_reference_exists(name, whole_text):
                out.append(Finding(
                    7, "unused-symbol", str(d.file), d.line,
                    f"{kind} '{name}' is defined here but never referenced "
                    f"anywhere else in the mod (dead code candidate)."
                ))
    return out


# ---------------------------------------------------------------------
# Vanilla (best-effort) corpus
# ---------------------------------------------------------------------

def find_vanilla_root(override: str | None) -> Path | None:
    if override:
        p = Path(override)
        return p if p.exists() else None
    for cand in VANILLA_CANDIDATES:
        if cand.exists():
            return cand
    return None


def build_vanilla_corpus(game_root: Path) -> Corpus:
    c = Corpus()
    in_game_common = game_root / "in_game" / "common"
    main_menu_common = game_root / "main_menu" / "common"
    targets = [
        (in_game_common / "building_types", c.buildings),
        (in_game_common / "religious_schools", c.religious_schools),
        (main_menu_common / "static_modifiers", c.modifiers),
        (in_game_common / "biases", c.biases),
    ]
    for folder, table in targets:
        if not folder.exists():
            continue
        for p in sorted(folder.rglob("*.txt")):
            raw = p.read_text(encoding="utf-8-sig", errors="replace")
            sf = SourceFile(p, raw, strip_comments(raw))
            table.update(scan_toplevel_defs(sf, TOPLEVEL_DEF_RE))

    # Vanilla localization, best-effort - this mod's own "0000_substitute_*"
    # event files override base-game events and rely on the BASE GAME's
    # own loc keys (e.g. flavor_ira.47.title), which never exist in this
    # mod's own yml files at all - without this, every one of those would
    # falsely report as missing.
    for loc_root in (game_root / "in_game" / "localization",
                      game_root / "main_menu" / "localization",
                      game_root / "loading_screen" / "localization"):
        eng = loc_root / "english"
        if not eng.exists():
            continue
        for p in sorted(eng.rglob("*.yml")):
            raw = p.read_text(encoding="utf-8-sig", errors="replace")
            for m in LOC_KEY_RE.finditer(raw):
                c.loc_keys.add(m.group(1))
    return c


# ---------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------

TIER_LABELS = {
    1: "Tier 1 - syntax (near-certain)",
    2: "Tier 2 - quoted $PARAM$ gotcha (near-certain)",
    3: "Tier 3 - unreferenced $PARAM$ at a call site (near-certain)",
    4: "Tier 4 - missing localization key (near-certain)",
    5: "Tier 5 - possibly-undefined aqd_/z_aqd_ identifier (review)",
    6: "Tier 6 - possibly-undefined building/school/modifier reference (review)",
    7: "Tier 7 - possibly-unused mod symbol (review)",
}


def relpath(p: str) -> str:
    try:
        return str(Path(p).relative_to(MOD_ROOT))
    except ValueError:
        return p


def print_report(findings: list[Finding]) -> None:
    by_tier: dict[int, list[Finding]] = {}
    for f in findings:
        by_tier.setdefault(f.tier, []).append(f)

    total = len(findings)
    print(f"lint_mod: {total} finding(s)\n")
    for tier in sorted(by_tier):
        items = by_tier[tier]
        print(f"== {TIER_LABELS[tier]} :: {len(items)} ==")
        for f in sorted(items, key=lambda x: (x.file, x.line)):
            print(f"  {relpath(f.file)}:{f.line}  {f.message}")
        print()

    tier1_4 = sum(len(by_tier.get(t, [])) for t in (1, 2, 3, 4))
    if tier1_4 == 0:
        print("No Tier 1-4 (near-certain) issues found.")
    else:
        print(f"{tier1_4} Tier 1-4 issue(s) found - these are worth fixing.")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--vanilla", help="path to the EU5 'game' install folder")
    ap.add_argument("--no-vanilla", action="store_true", help="skip vanilla cross-referencing entirely")
    ap.add_argument("--quiet", action="store_true", help="only print Tier 1-4 findings")
    args = ap.parse_args()

    c = build_corpus(MOD_ROOT)

    vanilla_corpus = None
    if not args.no_vanilla:
        vroot = find_vanilla_root(args.vanilla)
        if vroot:
            vanilla_corpus = build_vanilla_corpus(vroot)
            print(f"(vanilla cross-reference: using {vroot})\n")
        else:
            print("(vanilla cross-reference: game install not found - skipping Tier 6 vanilla checks; "
                  "pass --vanilla PATH to enable)\n")

    all_loc_keys = set(c.loc_keys) | (vanilla_corpus.loc_keys if vanilla_corpus else set())

    findings: list[Finding] = []
    findings += check_brace_balance(c.script_files)
    findings += check_quoted_param(c.script_files)
    findings += check_param_mismatch(c, c.script_files)
    findings += check_missing_loc(c, all_loc_keys, c.script_files)
    if not args.quiet:
        findings += check_undefined_aqd_calls(c, c.script_files)
        findings += check_reference_targets(c, c.script_files, vanilla_corpus)
        findings += check_unused_symbols(c, c.script_files)

    print_report(findings)

    tier1_4_count = sum(1 for f in findings if f.tier <= 4)
    return 1 if tier1_4_count else 0


if __name__ == "__main__":
    sys.exit(main())
