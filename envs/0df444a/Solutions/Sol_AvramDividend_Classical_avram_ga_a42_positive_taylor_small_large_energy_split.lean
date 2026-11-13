-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a42_positive_taylor_small_large_energy_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:41:53.923241+00:00
-- url     : https://prove2.me/submissions/90e560b4-285b-4dcb-a123-e745563509cd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

-- Positive C2 Taylor coefficients split into a small-modulus quadratic cost and a large-increment tail.
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (a z ε M δ : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hM : a ≤ M) (hSmall : |z| < δ → a ≤ ε) :
    a * z ^ 2 ≤
      ε * z ^ 2 + M * (if δ ≤ |z| then z ^ 2 else 0) := by
  have hz : 0 ≤ z ^ 2 := sq_nonneg z
  by_cases h : δ ≤ |z|
  · simp only [if_pos h]
    have hh := mul_le_mul_of_nonneg_right hM hz
    nlinarith
  · have he : a ≤ ε := hSmall (lt_of_not_ge h)
    simp only [if_neg h, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right he hz
