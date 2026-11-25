-- Prove2me | solution 1 for Formalism.RankGapBounds.ChebyshevFactorialBounds.cardLargePrimeFactorsLeOne_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:19:29.49138+00:00
-- url     : https://prove2.me/submissions/f4ffe2d3-8427-4d12-a45f-75392ffbdcd0

import Definitions.Def_Formalism_RankGapBounds_LargePrimeFactor
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Finset
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.RankGapBounds.ChebyshevFactorialBounds
theorem _root_.solution : LargePrimeFactor := by
  intro L z hL hz hzL
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at ha hb
  by_contra hne
  have hab : a * b ∣ z := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes ha.1.1 hb.1.1).mpr hne) ha.1.2.1 hb.1.2.1
  have hle : ((a * b : ℕ) : ℝ) ≤ z := by exact_mod_cast Nat.le_of_dvd (by omega) hab
  push_cast at hle
  have hLL : L * L < (a : ℝ) * b := mul_lt_mul'' ha.2 hb.2 hL hL
  rw [sq] at hzL
  linarith
end Formalism.RankGapBounds.ChebyshevFactorialBounds
