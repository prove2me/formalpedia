-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.wirtinger_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:51:59.46831+00:00
-- url     : https://prove2.me/submissions/cc2553a2-54f2-41b1-bfec-74b4693683fe

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirtingerIBP

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.WirtingerIBP := WirtingerIntegrationByParts.wirtingerIBP
end Formalism.FourierDecayAlt.P
