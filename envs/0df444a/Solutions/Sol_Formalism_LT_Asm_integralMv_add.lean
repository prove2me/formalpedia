-- Prove2me | solution 1 for Formalism.LT.Asm.integralMv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:31:47.288854+00:00
-- url     : https://prove2.me/submissions/b35eb24e-515f-43ae-a485-157c623ee3b0

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
theorem _root_.solution {ι : Type*} {a b : MvPowerSeries ι K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a + b) := by
  intro d
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) (hb d))
end Formalism.LT.Asm
