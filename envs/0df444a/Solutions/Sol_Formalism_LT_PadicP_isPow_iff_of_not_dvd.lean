-- Prove2me | solution 1 for Formalism.LT.PadicP.isPow_iff_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:50.060931+00:00
-- url     : https://prove2.me/submissions/52ab9250-98e5-4362-8af2-e4c2bcbc57fd

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
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.LT.PadicP
theorem _root_.solution (n : ℕ) (h : ¬ p ∣ n) : (∃ k : ℕ, p ^ k = n) ↔ n = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact pow_zero p
    | succ k => exact absurd (dvd_pow_self p (Nat.succ_ne_zero k)) h
  · rintro rfl
    exact ⟨0, pow_zero p⟩
end Formalism.LT.PadicP
