-- Prove2me | solution 1 for Formalism.LT.Asm.funEqType_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:02.791987+00:00
-- url     : https://prove2.me/submissions/42fbb6e6-b239-4951-940f-cef316374e0c

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
namespace Formalism.LT.Asm
theorem _root_.solution {K : Type u} [NormedField K] {p q : ℕ} (hq : q ≠ 0) {σ : K →+* K}
    {g : PowerSeries K} (hg : IsFunEqType p q σ g) :
    IsFunEqTypeMv (ι := Unit) p q hq σ (g : MvPowerSeries Unit K) := by
  have hx : (PowerSeries.map σ g).subst ((PowerSeries.X : PowerSeries K) ^ q) =
      MvPowerSeries.expand q hq (MvPowerSeries.map σ g) := by
    rw [← PowerSeries.expand_apply q hq]
    rfl
  intro d
  have := hg (d ())
  rw [hx] at this
  have hd : d = Finsupp.single () (d ()) := by
    ext
    simp
  rw [hd]
  exact this
end Formalism.LT.Asm
