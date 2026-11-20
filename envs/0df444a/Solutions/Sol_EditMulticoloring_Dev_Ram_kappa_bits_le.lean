-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.kappa_bits_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:53.988946+00:00
-- url     : https://prove2.me/submissions/a9e15d07-2431-4811-801e-88415c482b8d

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

theorem bits_mono {a b : ℕ} (h : a ≤ b) : RAM.bits a ≤ RAM.bits b := by
  unfold RAM.bits
  have := Nat.log_mono_right (b := 2) h
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  omega

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

/-- The standard way to bound a charge: the data is at most `M`. -/
theorem kappa_bits_le_oai (B : ℕ) {a M : ℕ} (h : a ≤ M) : kappa B (RAM.bits a) ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (bits_mono h)

/-! ## Syntactic frames -/

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.kappa_bits_le_oai := @EditMulticoloring.Dev.Ram.kappa_bits_le_oai
