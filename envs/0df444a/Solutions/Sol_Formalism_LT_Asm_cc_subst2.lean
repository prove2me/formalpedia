-- Prove2me | solution 1 for Formalism.LT.Asm.cc_subst2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:02.054805+00:00
-- url     : https://prove2.me/submissions/6927f2b5-afe0-41bc-88d1-2fc3fa1c48dc

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
theorem _root_.solution {R : Type*} [CommRing R] {τ : Type*} [Finite τ] (F : MvPowerSeries (Fin 2) R)
    (hF0 : MvPowerSeries.constantCoeff F = 0) {u v : MvPowerSeries τ R}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.constantCoeff (F.subst ![u, v]) = 0 := by
  have hc : ∀ s, MvPowerSeries.constantCoeff (![u, v] s) = 0 := by
    intro s
    fin_cases s <;> simp [hu, hv]
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hc) hc hF0
end Formalism.LT.Asm
