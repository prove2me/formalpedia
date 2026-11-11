-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite70_nonnegative_cap_fraction_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:17:57.767494+00:00
-- url     : https://prove2.me/submissions/c2563347-9b71-49ea-8f4c-335ab2568ac3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
noncomputable section

theorem solution (c : ℝ) (hc : 0 ≤ c) :
    Monotone (fun j : ℕ => c * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) := by
  apply monotone_nat_of_le_succ
  intro j
  apply mul_le_mul_of_nonneg_left _ hc
  have h1 : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
  have h2 : (0 : ℝ) < (((j + 1) + 2 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ h1 h2).2
  push_cast
  nlinarith
