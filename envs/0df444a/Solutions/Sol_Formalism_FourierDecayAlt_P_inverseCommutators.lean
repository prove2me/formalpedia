-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.inverseCommutators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:15.789011+00:00
-- url     : https://prove2.me/submissions/e95c79d4-a886-462c-99b0-7f95f4f82283

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_ruleInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.R.RuleInv := Formalism.FourierDecayAlt.R.PInv.ruleInv
end Formalism.FourierDecayAlt.P
