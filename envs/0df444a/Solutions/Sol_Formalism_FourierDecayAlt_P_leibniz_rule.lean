-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leibniz_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:43:56.793649+00:00
-- url     : https://prove2.me/submissions/2ef0f47c-1d6b-412d-adfb-8d8cfedeb682

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_leibniz


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
theorem _root_.solution : Formalism.FourierDecayAlt.LE.Leibniz := Formalism.FourierDecayAlt.P.LEx1.leibniz
end Formalism.FourierDecayAlt.P
