-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.inv_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:35.258178+00:00
-- url     : https://prove2.me/submissions/1e6af8ea-c153-4a0f-a53f-ea8d9aa3d36c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution (x : V) : (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ ≤ 4 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hA : (0 : ℝ) < (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) := by positivity
  have hB : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
  have hr : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have h3 : ((1 + ‖x‖) ^ 2) ^ 2 ≤ (2 * (1 + ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [hr, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB]
  nlinarith [h3]
end Formalism.FourierDecayAlt.P5.HerC.Fou
