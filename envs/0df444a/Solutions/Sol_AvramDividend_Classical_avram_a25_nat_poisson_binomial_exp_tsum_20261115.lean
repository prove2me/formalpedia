-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_nat_poisson_binomial_exp_tsum_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:31:59.964444+00:00
-- url     : https://prove2.me/submissions/4d9d2900-213e-4649-b506-9e122aa61063

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem solution (k : ℕ) (θ : ℝ) :
    (∑' n : ℕ, (Nat.choose k n : ℝ) * (Real.exp θ - 1) ^ n) =
      Real.exp (θ * (k : ℝ)) := by
  have hfinite :
      (∑' n : ℕ, (Nat.choose k n : ℝ) * (Real.exp θ - 1) ^ n) =
      ∑ n ∈ Finset.range (k + 1),
        (Nat.choose k n : ℝ) * (Real.exp θ - 1) ^ n := by
    apply tsum_eq_sum
    intro n hn
    have hkn : k < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    simp [Nat.choose_eq_zero_of_lt hkn]
  rw [hfinite]
  have hbin := (add_pow (Real.exp θ - 1) (1 : ℝ) k)
  simp only [one_pow, mul_one] at hbin
  calc
    (∑ n ∈ Finset.range (k + 1),
        (Nat.choose k n : ℝ) * (Real.exp θ - 1) ^ n) =
        ((Real.exp θ - 1) + 1) ^ k := by
      rw [hbin]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (Real.exp θ) ^ k := by ring
    _ = Real.exp (θ * (k : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
