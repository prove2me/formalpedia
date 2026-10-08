-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_rounding_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:40:36.275275+00:00
-- url     : https://prove2.me/submissions/7572b04e-aa3e-4191-b37c-89b35725d0f4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

theorem solution
    (t : ℝ≥0) (n : ℕ) :
    (t : ℝ) ≤
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n ∧
      (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n <
        (t : ℝ) + 1 / (2 : ℝ) ^ n := by
  have hscale : 0 < (2 : ℝ) ^ n := by positivity
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hprod : 0 ≤ (t : ℝ) * (2 : ℝ) ^ n :=
    mul_nonneg ht (le_of_lt hscale)
  have hlow :
      (t : ℝ) * (2 : ℝ) ^ n ≤
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) :=
    Nat.le_ceil _
  have hhigh :
      (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) <
        (t : ℝ) * (2 : ℝ) ^ n + 1 :=
    Nat.ceil_lt_add_one hprod
  constructor
  · apply (le_div_iff₀ hscale).mpr
    simpa only using hlow
  · apply (div_lt_iff₀ hscale).mpr
    have hdiv : (1 : ℝ) / (2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
      field_simp
    calc
      (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ) <
          (t : ℝ) * (2 : ℝ) ^ n + 1 := hhigh
      _ = ((t : ℝ) + 1 / (2 : ℝ) ^ n) * (2 : ℝ) ^ n := by
        rw [add_mul, hdiv]
