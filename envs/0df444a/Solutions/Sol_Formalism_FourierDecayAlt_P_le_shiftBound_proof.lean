-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.le_shiftBound_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:41.863821+00:00
-- url     : https://prove2.me/submissions/8e21090a-822d-418c-b251-b9b74eb95038

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_shiftBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.ShiftBound := Formalism.FourierDecayAlt.P.LEx1.shiftBound
end Formalism.FourierDecayAlt.P
