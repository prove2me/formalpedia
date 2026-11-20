-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.WordAt.congr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:32:53.222612+00:00
-- url     : https://prove2.me/submissions/d0fed220-259e-41ee-952e-ead1b06d18ee

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

theorem WordAt.congr_oai {q : ℕ} {s s' : HS} {x off : ℕ} {w : Word q} (h : WordAt s x off w)
    (h' : ∀ i < w.length, s'.arr x (off + i) = s.arr x (off + i)) : WordAt s' x off w := by
  intro i hi; rw [h' i hi, h i hi]

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.WordAt.congr_oai := @EditMulticoloring.Dev.Ram.WordAt.congr_oai
