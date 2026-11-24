-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.cv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:27.258985+00:00
-- url     : https://prove2.me/submissions/76c9861c-fced-4ac5-a8f7-68b5dbef17b1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_contDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
theorem _root_.solution (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]
end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
