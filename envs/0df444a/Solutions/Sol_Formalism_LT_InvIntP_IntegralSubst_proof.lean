-- Prove2me | solution 1 for Formalism.LT.InvIntP.IntegralSubst_proof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:29.662691+00:00
-- url     : https://prove2.me/submissions/e25d898b-7eef-4a5f-b402-49b0e88beca0

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Theorems.Thm_Formalism_LT_InvIntP_integralSubst

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
theorem _root_.solution : Formalism.LT.IntegralSubst.{u, v} := by
  intro K _ _ ι f P hf hP0 hP
  exact Formalism.LT.InvIntP.integralSubst f P hf hP0 hP
end Formalism.LT.InvIntP
