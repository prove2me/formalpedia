-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_negative_mark_poisson_weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:43:54.62257+00:00
-- url     : https://prove2.me/submissions/a9589697-830e-43db-9aac-2723c7c1b220

import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

/-- Literal intrinsic negative-mark weights match the Poisson PGF coefficient. -/
theorem solution (y : ℝ) (hy : y < 0) (n : ℕ) :
    Real.exp (-((n : ℝ) * (ENNReal.ofReal (-y)).toReal)) =
      (Real.exp y) ^ n := by
  have h_nonneg : 0 ≤ -y := by linarith
  rw [ENNReal.toReal_ofReal h_nonneg]
  have hmul : -((n : ℝ) * -y) = (n : ℝ) * y := by ring
  rw [hmul, Real.exp_nat_mul]
