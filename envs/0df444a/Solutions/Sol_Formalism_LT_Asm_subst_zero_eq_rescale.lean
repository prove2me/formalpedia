-- Prove2me | solution 1 for Formalism.LT.Asm.subst_zero_eq_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:03.559657+00:00
-- url     : https://prove2.me/submissions/d56f55e2-a148-4acc-9a5d-3a609670dd46

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
namespace Formalism.LT.Asm
theorem _root_.solution {R : Type*} [CommRing R] (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)] =
      MvPowerSeries.rescale ![0, 1] Φ := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  fin_cases s <;> simp
end Formalism.LT.Asm
