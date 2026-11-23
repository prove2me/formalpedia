-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.weighted_L2_bounded_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:40.08165+00:00
-- url     : https://prove2.me/submissions/06c93ecf-d43f-4fca-9d81-adb9004af548

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) (hwm : Measurable wt) (β f : B.Ω → ℂ) (C : ℝ)
    (hβm : Measurable β) (hβ : ∀ ω, ‖β ω‖ ≤ C) (hf : WeightedL2 B wt f) : WeightedL2 B wt (fun ω => β ω * f ω) := by
  refine ⟨hβm.aestronglyMeasurable.mul hf.1, ?_⟩
  refine Integrable.mono' (hf.2.const_mul (C ^ 2)) ?_ (Eventually.of_forall fun ω => ?_)
  · exact hwm.aestronglyMeasurable.mul ((hβm.aestronglyMeasurable.mul hf.1).norm.pow 2)
  · rw [Real.norm_of_nonneg (mul_nonneg (hw ω) (by positivity)), norm_mul, mul_pow]
    have h1 : ‖β ω‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hβ ω) 2
    calc _ = ‖β ω‖ ^ 2 * (wt ω * ‖f ω‖ ^ 2) := by ring
      _ ≤ C ^ 2 * (wt ω * ‖f ω‖ ^ 2) := mul_le_mul_of_nonneg_right h1 (mul_nonneg (hw ω) (by positivity))
end Formalism.FourierDecayAlt.P.LEx2
