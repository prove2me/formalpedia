-- Prove2me | solution 1 for Formalism.LT.IntegralSubst_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:51.922943+00:00
-- url     : https://prove2.me/submissions/08a8e73f-d95d-45a3-8021-1e26b6198946

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_IntegralSubst_proof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
namespace Formalism.LT
theorem _root_.solution : Formalism.LT.IntegralSubst.{u, v} := by
  exact Formalism.LT.InvIntP.IntegralSubst_proof
end Formalism.LT
