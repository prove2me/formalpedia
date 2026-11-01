-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:36:27.798568+00:00
-- url     : https://prove2.me/submissions/568f35f8-75d5-4038-97e6-f46f4ed4f7ed

import Mathlib.Analysis.Complex.Exponential

open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (θ a b : ℝ) (hθ : 0 ≤ θ) (hab : a ≤ b) :
    θ * Real.exp (-(θ * b)) * (b - a) ≤
      Real.exp (-(θ * a)) - Real.exp (-(θ * b)) := by
  have hh := Real.add_one_le_exp (θ * (b - a))
  have hpos : 0 ≤ Real.exp (-(θ * b)) := (Real.exp_pos _).le
  have hmul :
      Real.exp (-(θ * b)) * (θ * (b - a) + 1) ≤
        Real.exp (-(θ * b)) * Real.exp (θ * (b - a)) :=
    mul_le_mul_of_nonneg_left hh hpos
  rw [← Real.exp_add] at hmul
  have heq : -(θ * b) + θ * (b - a) = -(θ * a) := by ring
  rw [heq] at hmul
  nlinarith
