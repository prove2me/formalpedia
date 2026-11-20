-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.inputAt_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:29.300261+00:00
-- url     : https://prove2.me/submissions/729ae77d-cfb3-406c-a751-9f26022a4fcc

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine

section
-- module Solutions.EditMulticoloring.RamLib2
/-!
# Word utilities on `Cmd` (q379, Part L)

Each utility is a counted loop on registers given as parameters; every spec gives the effect,
the frame (registers outside the written list, memory, cursor, output) and a cost bound of the
form `(a * N + b) * kappa B (RAM.bits M)` under a data bound `… ≤ M`.

* `eqW`     — compare two stored blocks (flag register: 1 iff equal);
* `emitW`   — emit a stored block;
* `readW`   — read `N` input symbols, storing `v - 1`;
* `readRun` — the same, also computing the length of the leading non-EOF run (`runLen`);
* `valueW`  — Horner evaluation `V := q * V + a` (`= EditMulticoloring.Code.value`);
* `digitsW` — `D[off + i] := (V / Q ^ i) % Q` for `i < K`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ### Equality test -/

/-! ### Emitting a stored block -/

/-! ### Reading input -/

theorem inputAt_le_oai {q : ℕ} (y : Word q) (i : ℕ) : RAM.inputAt y i ≤ q := by
  unfold RAM.inputAt
  by_cases h : i < y.length
  · simp only [List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]
    have := (y[i]).isLt; omega
  · have h' : y.length ≤ i := by omega
    simp [List.getElem?_eq_none h']

/-! ### Horner evaluation -/

/-! ### Digits -/

end Utils

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.inputAt_le_oai := @EditMulticoloring.Dev.Ram.inputAt_le_oai
