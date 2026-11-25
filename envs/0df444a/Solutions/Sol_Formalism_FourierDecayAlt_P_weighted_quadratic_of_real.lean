-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weighted_quadratic_of_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:13.645314+00:00
-- url     : https://prove2.me/submissions/c315291b-871a-4542-8765-3c5cebf76d84

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_RealWeightedForms_qwOfReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.FormPairingAction.QwOfReal := Formalism.FourierDecayAlt.P.RealWeightedForms.qwOfReal
end Formalism.FourierDecayAlt.P
