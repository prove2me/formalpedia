-- Prove2me | solution 1 for Formalism.LT.Asm.psubst_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:32:02.885989+00:00
-- url     : https://prove2.me/submissions/e85a602a-5635-4615-9cbc-ca902fec6c71

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
theorem _root_.solution {R : Type*} [CommRing R] {τ : Type*} (f : PowerSeries R)
    (hf0 : constantCoeff f = 0) : f.subst (0 : MvPowerSeries τ R) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf0
  have ha : PowerSeries.HasSubst (0 : MvPowerSeries τ R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_X ha, zero_mul]
end Formalism.LT.Asm
