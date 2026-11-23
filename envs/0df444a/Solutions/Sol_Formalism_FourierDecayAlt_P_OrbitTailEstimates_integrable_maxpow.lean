-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.integrable_maxpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:17.494179+00:00
-- url     : https://prove2.me/submissions/3b92a6d6-88bb-4628-92ad-3c9aa57856d4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution (ν : Measure E) [ν.IsAddHaarMeasure] (B : ℝ)
    (hB : (Module.finrank ℝ E : ℝ) < B) : Integrable (fun q : E => (max 1 ‖q‖) ^ (-B)) ν := by
  have h0 : Integrable (fun q : E => (1 + ‖q‖) ^ (-B)) ν := integrable_one_add_norm hB
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) hB.le
  refine Integrable.mono' (h0.const_mul (2 ^ B)) ?_ (Filter.Eventually.of_forall fun q => ?_)
  · exact (Continuous.rpow_const (by fun_prop) (fun q => Or.inl (by positivity))).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (0 : ℝ) < 1 + ‖q‖ := by positivity
    have e : (2 : ℝ) ^ B * (1 + ‖q‖) ^ (-B) = ((1 + ‖q‖) / 2) ^ (-B) := by
      rw [Real.div_rpow h1.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) B]
      field_simp
    rw [e]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    have := le_max_left 1 ‖q‖
    have := le_max_right 1 ‖q‖
    linarith
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
