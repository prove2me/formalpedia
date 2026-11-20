-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.kappa_bits_one_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:55.033752+00:00
-- url     : https://prove2.me/submissions/4cab0659-94e2-4b12-ab97-4ae55064ccf4

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

theorem one_le_bits (a : ℕ) : 1 ≤ RAM.bits a := by unfold RAM.bits; omega

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

theorem kappa_one_le (B M : ℕ) : kappa B 1 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (one_le_bits M)

theorem kappa_bits_one_le_oai (B M : ℕ) : kappa B (RAM.bits 1) ≤ kappa B (RAM.bits M) := by
  rw [bits_one]; exact kappa_one_le B M

/-! ## Syntactic frames -/

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.kappa_bits_one_le_oai := @EditMulticoloring.Dev.Ram.kappa_bits_one_le_oai
