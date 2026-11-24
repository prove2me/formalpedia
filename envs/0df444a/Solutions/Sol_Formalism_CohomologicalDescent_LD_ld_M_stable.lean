-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_M_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:48.739971+00:00
-- url     : https://prove2.me/submissions/ef757fef-4389-476b-91cc-508293dadde1

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_one_zero_vector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_zero_one_vector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_zero_zero_vector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_one_one_vector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_M_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y : ℕ) (a b : Fin 2) (k : ℕ) (f : MvPolynomial (Fin 2 × Fin 2) ℤ)
    (hf : f ∈ ldM w y) : rowDiv ℤ a b k f ∈ ldM w y := by
  unfold ldM at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, hj, rfl⟩ := hf
    rw [rowDiv_smul]
    have ha : a = 0 ∨ a = 1 := by omega
    have hb : b = 0 ∨ b = 1 := by omega
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [divided_power_zero_zero_vector, smul_comm]
      exact Submodule.smul_mem _ _ (ld_M_gen w y j hj)
    · rw [divided_power_zero_one_vector w y j k hj]
      by_cases hk : k ≤ j
      · have hid : (w - y).choose j * j.choose k = (w - y - (j - k)).choose k * (w - y).choose (j - k) := by
          have h1 := Nat.choose_mul (n := w - y) (k := j) (s := j - k) (Nat.sub_le j k)
          rw [Nat.choose_symm hk, Nat.sub_sub_self hk] at h1
          rw [h1, mul_comm]
        rw [smul_smul]
        have hid' : (((w - y).choose j : ℕ) : ℤ) * ((j.choose k : ℕ) : ℤ) =
            (((w - y - (j - k)).choose k : ℕ) : ℤ) * (((w - y).choose (j - k) : ℕ) : ℤ) := by
          exact_mod_cast hid
        rw [hid', ← smul_smul]
        exact Submodule.smul_mem _ _ (ld_M_gen w y (j - k) (by omega))
      · rw [Nat.choose_eq_zero_of_lt (show j < k by omega)]
        simp
    · rw [divided_power_one_zero_vector]
      by_cases hk : y + (j + k) ≤ w
      · have hid : (w - y).choose j * (w - y - j).choose k = (j + k).choose j * (w - y).choose (j + k) := by
          have h1 := Nat.choose_mul (n := w - y) (k := j + k) (s := j) (Nat.le_add_right j k)
          rw [Nat.add_sub_cancel_left] at h1
          rw [← h1, mul_comm]
        rw [smul_smul]
        have hid' : (((w - y).choose j : ℕ) : ℤ) * (((w - y - j).choose k : ℕ) : ℤ) =
            (((j + k).choose j : ℕ) : ℤ) * (((w - y).choose (j + k) : ℕ) : ℤ) := by
          exact_mod_cast hid
        rw [hid', ← smul_smul]
        exact Submodule.smul_mem _ _ (ld_M_gen w y (j + k) hk)
      · rw [Nat.choose_eq_zero_of_lt (show w - y - j < k by omega)]
        simp
    · rw [divided_power_one_one_vector, smul_comm]
      exact Submodule.smul_mem _ _ (ld_M_gen w y j hj)
  | zero =>
    have : rowDiv ℤ a b k (0 : MvPolynomial (Fin 2 × Fin 2) ℤ) = 0 := (rowDivL ℤ a b k).map_zero
    rw [this]
    exact Submodule.zero_mem _
  | add x z _ _ hx hz =>
    rw [rowDiv_add]
    exact Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    rw [rowDiv_smul]
    exact Submodule.smul_mem _ _ hx
end Formalism.CohomologicalDescent.LD
