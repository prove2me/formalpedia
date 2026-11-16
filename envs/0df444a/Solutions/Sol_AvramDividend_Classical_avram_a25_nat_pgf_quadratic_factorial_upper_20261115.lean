-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_nat_pgf_quadratic_factorial_upper_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:12:03.998618+00:00
-- url     : https://prove2.me/submissions/4d0b5a7a-fe2d-43f9-b1a5-dcfc88ffd73a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The second falling factorial controls the Bernoulli PGF approximation. -/
theorem solution (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (k : ℕ) :
    z ^ k ≤ 1 - (1 - z) * (k : ℝ) +
      (1 - z) ^ 2 * (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
        by_cases h0 : k = 0
        · subst k
          norm_num
        · have h1 : (1 : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h0)
          exact mul_nonneg (by linarith) (by linarith)
      have hw : 0 ≤ 1 - z := sub_nonneg.mpr hz1
      have hc : 0 ≤ (1 - z) ^ 3 *
          ((k : ℝ) * ((k : ℝ) - 1)) / 2 :=
        div_nonneg (mul_nonneg (pow_nonneg hw 3) hk) (by norm_num)
      calc
        z ^ (k + 1) = z ^ k * z := pow_succ z k
        _ ≤ (1 - (1 - z) * (k : ℝ) +
          (1 - z) ^ 2 * (k : ℝ) * ((k : ℝ) - 1) / 2) * z :=
          mul_le_mul_of_nonneg_right ih hz0
        _ = (1 - (1 - z) * ((k + 1 : ℕ) : ℝ) +
          (1 - z) ^ 2 * ((k + 1 : ℕ) : ℝ) *
            (((k + 1 : ℕ) : ℝ) - 1) / 2) -
          (1 - z) ^ 3 * ((k : ℝ) * ((k : ℝ) - 1)) / 2 := by
            push_cast
            ring
        _ ≤ 1 - (1 - z) * ((k + 1 : ℕ) : ℝ) +
          (1 - z) ^ 2 * ((k + 1 : ℕ) : ℝ) *
            (((k + 1 : ℕ) : ℝ) - 1) / 2 := by linarith
