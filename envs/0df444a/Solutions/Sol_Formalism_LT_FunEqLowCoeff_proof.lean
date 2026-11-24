-- Prove2me | solution 1 for Formalism.LT.FunEqLowCoeff_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:14.310681+00:00
-- url     : https://prove2.me/submissions/40ba3e26-4abb-47c7-8bb8-fc6e06f8d78c

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_FunEqLowCoeff_proof

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
theorem _root_.solution : Formalism.LT.FunEqLowCoeff.{u, v} := by
  exact Formalism.LT.InvIntP.FunEqLowCoeff_proof
end Formalism.LT
