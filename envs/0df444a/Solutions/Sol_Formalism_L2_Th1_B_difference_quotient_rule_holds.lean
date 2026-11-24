-- Prove2me | solution 1 for Formalism.L2.Th1.B.difference_quotient_rule_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:59.674724+00:00
-- url     : https://prove2.me/submissions/3d2129a7-1f83-416c-b4f4-b41d3301a296

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_coeff_dq
import Theorems.Thm_Formalism_L2_Th1_B_eq_single_zero_iff
import Theorems.Thm_Formalism_L2_Th1_B_eq_single_one_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
namespace Formalism.L2.Th1.B
theorem _root_.solution : DqRule := by
  intro K _ _ P hodd
  have hc : ∀ m, ¬ Even m → PowerSeries.coeff m P = 0 := fun m hm => hodd m (Nat.not_even_iff_odd.1 hm)
  have hev : ∀ m, 2 ≤ m → (Even (m - 2) ↔ Even m) := by
    intro m hm
    rw [Nat.even_sub hm]
    simp
  have main : ∀ i j : ℕ, (if j = 0 then PowerSeries.coeff i P else 0) -
      (if i = 0 then PowerSeries.coeff j P else 0) =
      (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P else 0) else 0) -
      (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P else 0)
        else 0) := by
    intro i j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), sub_zero]
      rcases Nat.lt_or_ge i 2 with hi | hi
      · rw [if_neg (by omega : ¬ 2 ≤ i)]
        interval_cases i
        · simp
        · simp [hc 1 (by decide)]
      · rw [if_pos hi, if_neg (by omega : i ≠ 0), sub_zero, show i - 2 + 0 + 2 = i by omega]
        simp only [hev i hi]
        by_cases he : Even i
        · simp [he]
        · simp [he, hc i he]
    · rw [if_neg (by omega : j ≠ 0)]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), zero_sub, zero_sub]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · have : j = 1 := by omega
          subst this
          simp [hc 1 (by decide)]
        · rw [if_pos hj2, show 0 + (j - 2) + 2 = j by omega]
          simp only [hev j hj2]
          by_cases he : Even j
          · simp [he]
          · simp [he, hc j he]
      · rw [if_neg (by omega : i ≠ 0)]
        have t1 : (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P
            else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0 := by
          by_cases hi2 : 2 ≤ i
          · rw [if_pos hi2, show i - 2 + j + 2 = i + j by omega]
            simp only [hev i hi2]
          · have : i = 1 := by omega
            subst this
            simp
        have t2 : (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P
            else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0 := by
          by_cases hj2 : 2 ≤ j
          · rw [if_pos hj2, show i + (j - 2) + 2 = i + j by omega]
            simp only [hev j hj2]
          · have : j = 1 := by omega
            subst this
            simp
        rw [t1, t2]
        simp
  ext n
  rw [map_sub, coeff_single_variable_series, coeff_single_variable_series, sub_mul, map_sub, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_dq, coeff_dq]
  simp only [eq_single_zero_iff, eq_single_one_iff, Finsupp.single_le_iff, Finsupp.tsub_apply,
    Finsupp.single_apply, one_mul]
  simpa using main (n 0) (n 1)
end Formalism.L2.Th1.B
