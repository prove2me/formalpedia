-- Prove2me | solution 1 for Formalism.LT.ExpP.Formalism.LT.ExpP.QuasiLogShift_valid_direct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:16:58.174003+00:00
-- url     : https://prove2.me/submissions/30b90017-2f05-42c8-ba41-d5243e9bf98e

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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.ExpP
namespace Formalism.LT.ExpP
theorem _root_.solution : Formalism.LT.QuasiLogShift.{u} := quasiLogShift
end Formalism.LT.ExpP
end Formalism.LT.ExpP
