-- Prove2me | solution 1 for Formalism.LT.FunEqCongr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:01.142789+00:00
-- url     : https://prove2.me/submissions/5d0dc8c9-9760-4d88-98ea-599c6120d857

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_funEqCongr

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
universe u
namespace Formalism.LT
theorem _root_.solution (h5 : Formalism.LT.CoeffBound.{u}) (h6 : Formalism.LT.PowCongr.{u, 0}) :
    Formalism.G.FunEqCongr.{u} := Formalism.LT.CongrP.funEqCongr h5 h6
end Formalism.LT
