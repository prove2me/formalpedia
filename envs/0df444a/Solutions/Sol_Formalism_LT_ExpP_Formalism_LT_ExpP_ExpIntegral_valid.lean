-- Prove2me | solution 1 for Formalism.LT.ExpP.Formalism.LT.ExpP.ExpIntegral_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:26.905095+00:00
-- url     : https://prove2.me/submissions/c4c82d3b-e140-48e3-9cc1-f334778cad81

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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
namespace Formalism.LT.ExpP
theorem _root_.solution : Formalism.LT.ExpIntegral.{u} := expIntegral
end Formalism.LT.ExpP
end Formalism.LT.ExpP
