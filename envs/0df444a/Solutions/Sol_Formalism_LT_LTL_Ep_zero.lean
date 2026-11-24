-- Prove2me | solution 1 for Formalism.LT.LTL.Ep_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:59.484813+00:00
-- url     : https://prove2.me/submissions/fa201315-eed0-4beb-b928-c638c456a0c8

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Ep_sub

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
theorem _root_.solution [Finite ι] (e' : PowerSeries K) (he'0 : constantCoeff e' = 0) :
    Ep e' (0 : MvPowerSeries ι K) = 0 := by
  have := Ep_sub e' he'0 (0 : MvPowerSeries ι K) 0
  rw [sub_self, sub_self] at this
  exact this.symm
end Formalism.LT.LTL
