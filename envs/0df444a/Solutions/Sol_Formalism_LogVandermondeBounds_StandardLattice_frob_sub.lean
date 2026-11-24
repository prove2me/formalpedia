-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.frob_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:45.521586+00:00
-- url     : https://prove2.me/submissions/364ad13b-c71b-44f7-a4a3-7cb0332fc318

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] {q : ℕ}
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (hq : Fintype.card L = q ^ 2) (a b : L) : (a - b) ^ q = a ^ q - b ^ q := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card L (ringChar L)
  have hd : q ∣ ringChar L ^ (n : ℕ) := by
    rw [← hn, hq]; exact Dvd.intro _ (pow_two q).symm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
  subst hk
  have : Fact (ringChar L).Prime := ⟨hp⟩
  exact sub_pow_char_pow a b k
end Formalism.LogVandermondeBounds.StandardLattice
