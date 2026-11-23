-- Prove2me | solution 1 for Formalism.LT.exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:38.984052+00:00
-- url     : https://prove2.me/submissions/f6997280-4c30-4f34-81c2-57033e5c5ef6

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_LT_ExpP_expIntegral

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
theorem _root_.solution : Formalism.LT.ExpIntegral.{u} := Formalism.LT.ExpP.expIntegral
end Formalism.LT
