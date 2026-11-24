-- Prove2me | solution 1 for Formalism.L2.Th1.B.Wr.eq_zero_of_wronsk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:54.813604+00:00
-- url     : https://prove2.me/submissions/6c4cacf3-7703-4faa-8da3-470a44743896

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_XTwoDvdOfRestrictThirdZero
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_mul
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_add
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_natCast
import Theorems.Thm_Formalism_L2_Th1_B_Wr_restrictThirdZero_X_two
import Theorems.Thm_Formalism_L2_Th1_B_Wr_X_two_dvd_of_restrictThirdZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
private theorem X_two_fin_three_ne_zero : (X 2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single (2 : Fin 3) 1)) h
  simp [coeff_X] at this
private theorem pderiv_X_fin_three_self (i : Fin 3) :
    MvPowerSeries.pderiv K i (X i : MvPowerSeries (Fin 3) K) = 1 := by
  simp
private theorem pderiv_two_X_two_pow_succ (m : ℕ) :
    MvPowerSeries.pderiv K 2 ((X 2 : MvPowerSeries (Fin 3) K) ^ (m + 1)) =
      ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (X 2 : MvPowerSeries (Fin 3) K) (m + 1), Derivation.leibniz, ih, pderiv_X_fin_three_self]
    simp only [smul_eq_mul]
    push_cast
    ring
private theorem pd_two_X_two_pow_succ_mul (m : ℕ) (R : MvPowerSeries (Fin 3) K) :
    Formalism.L2.Th1.B.pd 2 (X 2 ^ (m + 1) * R) =
      X 2 ^ (m + 1) * Formalism.L2.Th1.B.pd 2 R + R * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m) := by
  unfold Formalism.L2.Th1.B.pd
  rw [Derivation.leibniz, pderiv_two_X_two_pow_succ]
  simp only [smul_eq_mul]
end Formalism.L2.Th1.B.Wr
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Wr
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Wr
theorem _root_.solution {Q B : MvPowerSeries (Fin 3) K} (hw : Q * pd 2 B = B * pd 2 Q)
    (hQ : ev3 Q = 0) (hB : ev3 B ≠ 0) : Q = 0 := by
  have key : ∀ m : ℕ, ∃ R : MvPowerSeries (Fin 3) K, Q = X 2 ^ (m + 1) * R := by
    intro m
    induction m with
    | zero =>
      obtain ⟨R, hR⟩ := X_two_dvd_of_restrictThirdZero hQ
      exact ⟨R, by rw [hR]; ring⟩
    | succ m ih =>
      obtain ⟨R, rfl⟩ := ih
      rw [pd_two_X_two_pow_succ_mul] at hw
      have h1 : X 2 ^ m * (X 2 * R * Formalism.L2.Th1.B.pd 2 B) =
          X 2 ^ m * (B * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * R + X 2 * Formalism.L2.Th1.B.pd 2 R)) := by
        linear_combination hw
      have h2 := mul_left_cancel₀ (pow_ne_zero m X_two_fin_three_ne_zero) h1
      have h3 := congrArg Formalism.L2.Th1.B.ev3 h2
      simp only [restrictThirdZero_mul, restrictThirdZero_add, restrictThirdZero_X_two,
        restrictThirdZero_natCast, zero_mul, add_zero] at h3
      have hc : ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) ≠ 0 := by
        intro hc
        have := congrArg (coeff (0 : Fin 3 →₀ ℕ)) hc
        simp at this
        exact Nat.cast_add_one_ne_zero m this
      have hR : Formalism.L2.Th1.B.ev3 R = 0 := by
        rcases mul_eq_zero.mp h3.symm with h | h
        · exact absurd h hB
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hc
          · exact h
      obtain ⟨S, hS⟩ := X_two_dvd_of_restrictThirdZero hR
      exact ⟨S, by rw [hS]; ring⟩
  ext n
  obtain ⟨R, hR⟩ := key (n 2)
  suffices hz : coeff n ((X 2 : MvPowerSeries (Fin 3) K) ^ (n 2 + 1) * R) = 0 by
    rw [hR, hz]; simp
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hpq' : p + q = n := by simpa using hpq
  rw [coeff_X_pow]
  split_ifs with hp
  · exfalso
    subst hp
    have := DFunLike.congr_fun hpq' 2
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · simp
end Formalism.L2.Th1.B.Wr
