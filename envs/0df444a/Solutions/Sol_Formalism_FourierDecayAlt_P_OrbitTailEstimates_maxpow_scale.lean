-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.maxpow_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:30.059838+00:00
-- url     : https://prove2.me/submissions/68ed0dae-682e-4aa4-a895-c06f0e3b03a8

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
theorem _root_.solution (T A : ℝ) (hT : 0 < T) (q : E) :
    (max T ‖q‖) ^ (-A) = T ^ (-A) * (max 1 ‖T⁻¹ • q‖) ^ (-A) := by
  have e : max T ‖q‖ = T * max 1 ‖T⁻¹ • q‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hT.le), mul_max_of_nonneg _ _ hT.le, mul_one,
      mul_inv_cancel_left₀ hT.ne']
  rw [e, Real.mul_rpow hT.le (by positivity)]
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
