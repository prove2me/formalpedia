-- Prove2me | solution 1 for Formalism.LT.InvIntP.FunEqLowCoeff_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:54.887309+00:00
-- url     : https://prove2.me/submissions/4a277b31-f168-4679-97bc-d221cd7ab0a4

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_funEqLowCoeff

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
theorem _root_.solution : Formalism.LT.FunEqLowCoeff.{u, v} := by
  intro K _ ι p q hq σ hq2 D hD N hN hlow d hd
  exact Formalism.LT.InvIntP.funEqLowCoeff p q hq σ hq2 D hD N hN hlow d hd
end Formalism.LT.InvIntP
