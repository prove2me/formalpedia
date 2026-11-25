-- Prove2me | solution 1 for Formalism.LT.QuasiLogShift_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:14:58.843932+00:00
-- url     : https://prove2.me/submissions/ddd0c32a-4444-42b5-bb87-3ead2bbf76ff

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Theorems.Thm_Formalism_LT_ExpP_quasiLogShift

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
theorem _root_.solution : Formalism.LT.QuasiLogShift.{u} := Formalism.LT.ExpP.quasiLogShift
end Formalism.LT
