-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_nat_factorial_exp_tsum_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:42:46.517802+00:00
-- url     : https://prove2.me/submissions/06dca578-c7da-451b-80c7-72f57067c5a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_nat_poisson_binomial_exp_tsum_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- The descending-factorial expansion of a natural-count exponential. -/
theorem solution (k : ℕ) (θ : ℝ) :
    (∑' n : ℕ,
      (Nat.descFactorial k n : ℝ) *
        ((Real.exp θ - 1) ^ n / (n.factorial : ℝ))) =
    Real.exp (θ * (k : ℝ)) := by
  calc
    (∑' n : ℕ, (Nat.descFactorial k n : ℝ) *
        ((Real.exp θ - 1) ^ n / (n.factorial : ℝ))) =
      ∑' n : ℕ, (Nat.choose k n : ℝ) * (Real.exp θ - 1) ^ n := by
        apply tsum_congr
        intro n
        have hn : (n.factorial : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero n
        rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
        field_simp
    _ = Real.exp (θ * (k : ℝ)) :=
      avram_a25_nat_poisson_binomial_exp_tsum_20261115 k θ
