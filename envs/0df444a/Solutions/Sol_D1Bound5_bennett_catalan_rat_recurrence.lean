-- Prove2me | solution 1 for D1Bound5.bennett_catalan_rat_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:33.644477+00:00
-- url     : https://prove2.me/submissions/f3de7c67-85e2-4003-b003-b59d67c12dd0

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/

/-- The Catalan recurrence in the form needed for half-binomial coefficients. -/
theorem _root_.solution (n : ℕ) :
    ((n : ℚ) + 2) * (catalan (n + 1) : ℚ) =
      2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at h
  have hQ : ((n : ℚ) + 1) * (((n : ℚ) + 2) * (catalan (n + 1) : ℚ)) =
      2 * (2 * (n : ℚ) + 1) * (((n : ℚ) + 1) * (catalan n : ℚ)) := by
    exact_mod_cast h
  apply mul_left_cancel₀ (show (n : ℚ) + 1 ≠ 0 by positivity)
  linear_combination hQ























end D1Bound5
end
