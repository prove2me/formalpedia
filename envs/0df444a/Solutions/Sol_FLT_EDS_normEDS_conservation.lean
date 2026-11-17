-- Prove2me | solution 1 for FLT.EDS.normEDS_conservation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:43.965955+00:00
-- url     : https://prove2.me/submissions/2853a146-656a-4eb3-8738-126b05f08546

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardConservation
import Theorems.Thm_FLT_EDS_normEDS_adjacent_somos
import Definitions.Def_WardSomos

/-! Proofs of the lemmas stated in `Theorems.Thm_EDS_NumeratorDenominatorSequences` and their helpers. -/
namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- Conservation step: `N_{n+1} D_n = N_n D_{n+1}`, a finite `linear_combination` of the adjacent
Somos at `n` and `n+1` (cofactors from sympy Gröbner, remainder 0). -/
theorem _root_.solution (b c d : R) (n : ℤ) :
    Nseq b c d (n+1) * Dseq b c d n = Nseq b c d n * Dseq b c d (n+1) := by
  have s0 := normEDS_adjacent_somos b c d n
  have s1 := normEDS_adjacent_somos b c d (n+1)
  simp only [show (n+1)+2 = n+3 by ring, show (n+1)-2 = n-1 by ring,
    show (n+1)+1 = n+2 by ring, show (n+1)-1 = n by ring] at s1 ⊢
  unfold Nseq Dseq
  simp only [show (n+1)+2 = n+3 by ring, show (n+1)-1 = n by ring,
    show (n+1)+1 = n+2 by ring, show (n+1)-2 = n-1 by ring]
  linear_combination
    (- normEDS b c d n * normEDS b c d (n+1)^3) * s0
    + (normEDS b c d n ^ 3 * normEDS b c d (n+1)) * s1

end FLT.EDS
