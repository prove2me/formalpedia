-- Prove2me | solution 1 for Formalism.LT.InvIntP.InvIntegralOfClass_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:49.035326+00:00
-- url     : https://prove2.me/submissions/ae252113-cbc6-43f7-a6ea-76b8e3ff8106

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_invIntegralOfClass

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
namespace Formalism.LT.InvIntP
theorem _root_.solution : Formalism.LT.InvIntegralOfClass.{u, v} := by
  intro K _ _ ι _ C f h0 h1 hsub hP hlowC h hh0 hCh
  exact Formalism.LT.InvIntP.invIntegralOfClass K ι C f h0 h1 hsub hP hlowC h hh0 hCh
end Formalism.LT.InvIntP
