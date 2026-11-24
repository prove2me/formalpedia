-- Prove2me | solution 1 for Formalism.LT.Asm.map_subst2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:01.44032+00:00
-- url     : https://prove2.me/submissions/3ab5e8ee-202b-4fcc-8099-5dfbdc91561a

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
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {τ : Type*}
    (Φ : MvPowerSeries (Fin 2) A) {u v : MvPowerSeries τ A}
    (hu : MvPowerSeries.constantCoeff u = 0) (hv : MvPowerSeries.constantCoeff v = 0) :
    MvPowerSeries.map φ (Φ.subst ![u, v]) =
      (MvPowerSeries.map φ Φ).subst ![MvPowerSeries.map φ u, MvPowerSeries.map φ v] := by
  have hc : ∀ s, MvPowerSeries.constantCoeff (![u, v] s) = 0 := by
    intro s
    fin_cases s <;> simp [hu, hv]
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hc)]
  congr 1
  funext s
  fin_cases s <;> rfl
end Formalism.LT.Asm
