-- Prove2me | solution 1 for Formalism.LT.Asm.map_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:00.415029+00:00
-- url     : https://prove2.me/submissions/27fdf928-2e6e-4180-83f0-f50bdf1df956

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
import Theorems.Thm_Formalism_LT_Asm_coeff_lift

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
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G
open Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.Asm
theorem _root_.solution {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) :
    MvPowerSeries.map (unitBall K).subtype (lift F hF) = F := by
  ext d
  rw [MvPowerSeries.coeff_map]
  exact coeff_lift F hF d
end Formalism.LT.Asm
