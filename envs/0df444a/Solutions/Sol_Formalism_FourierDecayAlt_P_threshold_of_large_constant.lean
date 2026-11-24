-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.threshold_of_large_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:27:17.927436+00:00
-- url     : https://prove2.me/submissions/db63650e-bb8b-4a13-a7d7-8de07ab364e6

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdOfLargeConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {k r CV : ℕ} {A : ℝ} (hr : 1 ≤ r) (hCV : 19 ≤ CV)
    (hA : (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  unfold AV at hA
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hCV' : (19 : ℝ) ≤ CV := by exact_mod_cast hCV
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  rw [lt_div_iff₀ (by positivity)]
  have h1 : (r : ℝ) * ((CV : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) ≤ A := by
    refine le_trans ?_ hA
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : 0 ≤ (r : ℝ) ^ 3 * ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
    have : 0 ≤ (r : ℝ) ^ 4 := by positivity
    linarith
  have h2 : (r : ℝ) * (19 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) ≤
      (r : ℝ) * ((CV : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hCV' (by positivity)
  have h3 : 0 ≤ ((r : ℝ) - 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h4 : 0 < (r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith
end Formalism.FourierDecayAlt.P
