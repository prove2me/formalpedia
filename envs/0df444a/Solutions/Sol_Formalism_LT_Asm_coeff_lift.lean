-- Prove2me | solution 1 for Formalism.LT.Asm.coeff_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:06.461206+00:00
-- url     : https://prove2.me/submissions/ac28f678-53f7-478e-a2bb-716709e1747f

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
theorem _root_.solution {τ : Type*} (F : MvPowerSeries τ K) (hF : IntegralMv F) (d : τ →₀ ℕ) :
    ((MvPowerSeries.coeff d (lift F hF) : unitBall K) : K) = MvPowerSeries.coeff d F := rfl
end Formalism.LT.Asm
