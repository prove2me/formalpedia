-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.words_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:59.014179+00:00
-- url     : https://prove2.me/submissions/43d1cd77-e6c9-4f2f-9794-c649d12cbc8c

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

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

/-- Equal stored words of equal length: the flag is `1` iff the words are equal. -/
theorem words_eq_iff_oai {q : ℕ} (s : HS) (x ox y oy : ℕ) (w w' : Word q) (hw : WordAt s x ox w)
    (hw' : WordAt s y oy w') (hl : w.length = w'.length) :
    (∀ i < w.length, s.arr x (ox + i) = s.arr y (oy + i)) ↔ w = w' := by
  constructor
  · intro h
    apply List.ext_getElem hl
    intro i h1 h2
    apply Fin.ext
    rw [← hw i h1, ← hw' i h2]; exact h i h1
  · rintro rfl i hi; rw [hw i hi, hw' i hi]

/-! ### Emitting a stored block -/

/-! ### Reading input -/

/-! ### Horner evaluation -/

/-! ### Digits -/

end Utils

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.words_eq_iff_oai := @EditMulticoloring.Dev.Ram.words_eq_iff_oai
