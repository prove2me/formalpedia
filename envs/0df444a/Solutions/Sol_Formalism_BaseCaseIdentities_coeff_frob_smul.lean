-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.coeff_frob_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:46.068488+00:00
-- url     : https://prove2.me/submissions/d0f5ce79-8415-47f1-bd92-253d2374991d

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
namespace Formalism.BaseCaseIdentities
theorem _root_.solution {k : Type*} [Field k] {Z : Type*} (N : ℕ) (hN : 1 ≤ N)
    (f : MvPowerSeries Z k) (A : Z →₀ ℕ) : coeff (N • A) (frob N f) = (coeff A f) ^ N := by
  have h1 : ∀ d, N ∣ (N • A) d := fun d => by simp
  have h2 : (N • A).mapRange (· / N) (Nat.zero_div N) = A := by
    ext d
    simp [Nat.mul_div_cancel_left _ hN]
  show (if ∀ d, N ∣ (N • A) d then
    (coeff ((N • A).mapRange (· / N) (Nat.zero_div N)) f) ^ N else 0) = _
  rw [if_pos h1, h2]
end Formalism.BaseCaseIdentities
