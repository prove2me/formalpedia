-- Prove2me | solution 1 for D1Bound5.bennett_half_choose_scaled_catalan
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:03.590371+00:00
-- url     : https://prove2.me/submissions/55ed7df1-7a47-4c3f-b75e-9c16a7e269d1

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Theorems.Thm_D1Bound5_bennett_catalan_rat_recurrence

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/



/-- The generalized choose recurrence, specialized to one half. -/
theorem bennett_half_choose_rat_recurrence (n : ℕ) :
    ((n : ℚ) + 1) * Ring.choose (1 / 2 : ℚ) (n + 1) =
      ((1 / 2 : ℚ) - n) * Ring.choose (1 / 2 : ℚ) n := by
  have h := Ring.choose_smul_choose (r := (1 / 2 : ℚ))
    (n := n + 1) (k := n) (Nat.le_succ n)
  simpa [Nat.choose_succ_self_right, nsmul_eq_mul, Ring.choose_one_right,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- Exact Catalan formula: multiplying the positive-degree half-binomial
coefficient by 4 to its degree gives twice a signed Catalan integer. -/
theorem _root_.solution (n : ℕ) :
    (4 : ℚ) ^ (n + 1) * Ring.choose (1 / 2 : ℚ) (n + 1) =
      (-1 : ℚ) ^ n * 2 * (catalan n : ℚ) := by
  induction n with
  | zero => norm_num [Ring.choose_one_right]
  | succ n ih =>
      have hrec : ((n : ℚ) + 2) * Ring.choose (1 / 2 : ℚ) (n + 2) =
          ((1 / 2 : ℚ) - ((n : ℚ) + 1)) *
            Ring.choose (1 / 2 : ℚ) (n + 1) := by
        convert bennett_half_choose_rat_recurrence (n + 1) using 1 <;>
          simp only [Nat.cast_add, Nat.cast_one] <;> ring
      have hcat := bennett_catalan_rat_recurrence n
      change (4 : ℚ) ^ (n + 2) * Ring.choose (1 / 2 : ℚ) (n + 2) =
        (-1 : ℚ) ^ (n + 1) * 2 * (catalan (n + 1) : ℚ)
      apply mul_left_cancel₀ (show (n : ℚ) + 2 ≠ 0 by positivity)
      calc
        ((n : ℚ) + 2) * ((4 : ℚ) ^ (n + 2) *
            Ring.choose (1 / 2 : ℚ) (n + 2)) =
            (4 : ℚ) ^ (n + 2) * (((n : ℚ) + 2) *
              Ring.choose (1 / 2 : ℚ) (n + 2)) := by ring
        _ = (4 : ℚ) ^ (n + 2) * (((1 / 2 : ℚ) - ((n : ℚ) + 1)) *
            Ring.choose (1 / 2 : ℚ) (n + 1)) := by rw [hrec]
        _ = (-2 * (2 * (n : ℚ) + 1)) *
            ((4 : ℚ) ^ (n + 1) * Ring.choose (1 / 2 : ℚ) (n + 1)) := by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          ring
        _ = ((n : ℚ) + 2) * ((-1 : ℚ) ^ (n + 1) * 2 *
            (catalan (n + 1) : ℚ)) := by
          rw [ih, pow_succ]
          linear_combination (2 * (-1 : ℚ) ^ n) * hcat



















end D1Bound5
end
