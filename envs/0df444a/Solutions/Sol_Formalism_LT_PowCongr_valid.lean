-- Prove2me | solution 1 for Formalism.LT.PowCongr_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:35:21.787827+00:00
-- url     : https://prove2.me/submissions/8ce14851-ebdc-4a62-ae29-46ba9cddb99f

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Theorems.Thm_Formalism_LT_CoeffP_powCongr

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
theorem _root_.solution : Formalism.LT.PowCongr.{u, v} := Formalism.LT.CoeffP.powCongr
end Formalism.LT
