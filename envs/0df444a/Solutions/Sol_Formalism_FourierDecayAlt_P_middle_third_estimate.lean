-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.middle_third_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:34.214226+00:00
-- url     : https://prove2.me/submissions/45d42411-c808-4792-9f1c-0413e0f4f8c1

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_E2_middleThird_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.E.MiddleThird := Formalism.FourierDecayAlt.P.E2.middleThird_ok
end Formalism.FourierDecayAlt.P
