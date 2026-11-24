-- Prove2me | solution 1 for Formalism.LT.Asm.map_subtype_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:02.171365+00:00
-- url     : https://prove2.me/submissions/29901c49-4457-44d8-aad5-68e6feb666da

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective

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
theorem _root_.solution {τ : Type*} :
    Function.Injective
      (MvPowerSeries.map (unitBall K).subtype : MvPowerSeries τ (unitBall K) → MvPowerSeries τ K) := by
  intro a b h
  ext d
  have h' := congrArg (MvPowerSeries.coeff d) h
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h'
  exact h'
end Formalism.LT.Asm
