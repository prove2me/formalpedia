-- Prove2me | solution 1 for Formalism.LT.LTL.Ldef_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:49:27.571335+00:00
-- url     : https://prove2.me/submissions/41fae27f-092a-45f1-b7f5-8566c4b898c9

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Ep_zero

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
theorem _root_.solution [Finite ι] (e e' : PowerSeries K) (he0 : constantCoeff e = 0)
    (he'0 : constantCoeff e' = 0) : Ldef e e' (0 : MvPowerSeries ι K) = 0 := by
  unfold Ldef
  rw [Ep_zero e' he'0, PowerSeries.subst_zero_of_constantCoeff_zero he0, sub_zero]
end Formalism.LT.LTL
