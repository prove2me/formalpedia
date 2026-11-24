-- Prove2me | solution 1 for Formalism.LT.LTL.dv_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:34.793501+00:00
-- url     : https://prove2.me/submissions/caf78dcd-cea0-49ef-8473-33d78ed30107

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

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
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution {c : K} {A : MvPowerSeries ι K} (hA : DivByMv c A) :
    DivByMv c (-A) := fun d => by rw [map_neg, norm_neg]; exact hA d
end Formalism.LT.LTL
