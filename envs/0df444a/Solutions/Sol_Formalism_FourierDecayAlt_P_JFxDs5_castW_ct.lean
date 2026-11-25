-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs5.castW_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:21.889215+00:00
-- url     : https://prove2.me/submissions/602c7794-f3f5-4f5a-8c47-3d25adcf1490

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxDs5
theorem _root_.solution (a : B.Mat k 0) : (castW a)ᴴ = castW aᴴ := by
  unfold castW
  simp
end Formalism.FourierDecayAlt.P.JFxDs5
