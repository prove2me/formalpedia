-- Prove2me | solution 1 for Formalism.LT.Asm.integralMv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:03.527213+00:00
-- url     : https://prove2.me/submissions/0f451eb3-8d75-4da4-901e-b43cf1366bb0

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.Asm
theorem _root_.solution {ι : Type*} (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
end Formalism.LT.Asm
