-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cauchy_schwarz_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:39:46.323619+00:00
-- url     : https://prove2.me/submissions/faf5de18-b5a0-4485-9ae1-11630abedb01

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EnergyEstimateFromParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_csTerm


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
theorem _root_.solution : Formalism.FourierDecayAlt.LE.CSTerm := Formalism.FourierDecayAlt.P.LEx1.csTerm
end Formalism.FourierDecayAlt.P
