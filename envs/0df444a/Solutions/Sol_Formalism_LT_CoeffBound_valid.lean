-- Prove2me | solution 1 for Formalism.LT.CoeffBound_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:55.449918+00:00
-- url     : https://prove2.me/submissions/150da781-86ff-45c0-88f2-8b8b0d95f921

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_coeffBound

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
theorem _root_.solution : Formalism.LT.CoeffBound.{u} := Formalism.LT.CoeffP.coeffBound
end Formalism.LT
