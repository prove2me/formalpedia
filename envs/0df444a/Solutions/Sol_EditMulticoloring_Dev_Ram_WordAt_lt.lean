-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.WordAt.lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:54.763881+00:00
-- url     : https://prove2.me/submissions/d931d417-b9b4-4b8c-8765-453c2e43357c

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamLib
/-!
# Program-proof library for `Cmd` (q379, Part L)

* `simp` lemmas for `Cmd.exec` / `Cmd.cost` of every constructor and convenience constructor;
* `HS.setR` (register update) and `HS.arr` lemmas;
* syntactic frames: `Cmd.wregs` (registers possibly written), `Cmd.reads`, `Cmd.emits`, `Cmd.stores`;
* monotonicity of `kappa` and `RAM.bits`;
* the general loop lemma `loop_spec`, the counted for-loop `forLoop` with `forLoop_spec`
  (invariant + cost) and its list-fold form `forLoop_fold`;
* `copyW`, a word copy between (array, offset) places.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## States -/

/-! ## Small rewriting helpers (use with `simp (disch := omega)`) -/

/-! ## `exec` and `cost` of the constructors -/

/-! ## Monotonicity of the charges -/

/-! ## Syntactic frames -/

/-! ## Loops -/

/-! ## Words stored in arrays -/

theorem WordAt.lt_oai {q : ℕ} {s : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w) :
    ∀ i < w.length, s.arr x (off + i) < q := by
  intro i hi; rw [h i hi]; exact (w[i]).isLt

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.WordAt.lt_oai := @EditMulticoloring.Dev.Ram.WordAt.lt_oai
