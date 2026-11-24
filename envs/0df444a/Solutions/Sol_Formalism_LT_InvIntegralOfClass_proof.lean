-- Prove2me | solution 1 for Formalism.LT.InvIntegralOfClass_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:37.957988+00:00
-- url     : https://prove2.me/submissions/c0271606-fad6-45b8-86e1-506c69b29cf1

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_InvIntegralOfClass_proof

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
theorem _root_.solution : Formalism.LT.InvIntegralOfClass.{u, v} := by
  exact Formalism.LT.InvIntP.InvIntegralOfClass_proof
end Formalism.LT
