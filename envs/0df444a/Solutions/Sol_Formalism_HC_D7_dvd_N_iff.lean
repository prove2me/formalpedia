-- Prove2me | solution 1 for Formalism.HC.D7.dvd_N_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:56.672721+00:00
-- url     : https://prove2.me/submissions/d5e25622-0630-4d13-ade2-a1f30ab030b2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution {l : ℕ} (hl : l.Prime) : l ∣ 2 ^ (e + 2) * q * d ↔ l = 2 ∨ l = q ∨ l = d := by
  constructor
  · intro h
    rcases hl.dvd_mul.mp h with h | h
    · rcases hl.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hl hH.1).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hl hH.2.1).mp h))
  · rintro (rfl | rfl | rfl)
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _
    · exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
    · exact dvd_mul_left _ _
end Formalism.HC.D7
