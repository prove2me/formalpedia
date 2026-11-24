-- Prove2me | solution 1 for Formalism.LT.PadicP.isPow_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:33:20.428495+00:00
-- url     : https://prove2.me/submissions/0d75035d-c37d-4fe9-8fba-91424ea37c67

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
theorem _root_.solution (m : ℕ) : (∃ k : ℕ, p ^ k = p * m) ↔ ∃ k : ℕ, p ^ k = m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      rw [pow_zero] at hk
      have h1 : p ∣ 1 := ⟨m, hk⟩
      exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.out.two_le; omega)
    | succ k =>
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← pow_succ']; exact hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, pow_succ' p k⟩
end Formalism.LT.PadicP
