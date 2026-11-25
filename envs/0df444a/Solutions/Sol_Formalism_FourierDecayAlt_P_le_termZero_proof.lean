-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.le_termZero_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:52.83342+00:00
-- url     : https://prove2.me/submissions/b3425eb5-4b5b-49b8-9918-3e5c77ba0b27

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_termZero


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
theorem _root_.solution : Formalism.FourierDecayAlt.LE.TermZero := Formalism.FourierDecayAlt.P.LEx1.termZero
end Formalism.FourierDecayAlt.P
