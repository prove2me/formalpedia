-- Prove2me | solution 1 for Formalism.LT.PadicP.map_coe_injective_mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:38.481034+00:00
-- url     : https://prove2.me/submissions/c4be772d-8253-4aa0-8485-b183b18fbba6

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul

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
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
namespace Formalism.LT.PadicP
theorem _root_.solution {p : ℕ} [Fact p.Prime] {σ : Type} :
    Function.Injective (MvPowerSeries.map (σ := σ) (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])) := by
  intro x y h
  exact funext fun n => Subtype.ext (congrFun h n)
end Formalism.LT.PadicP
