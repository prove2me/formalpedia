-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_drift_small_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:21:17.371552+00:00
-- url     : https://prove2.me/submissions/0031cb70-a87a-43f2-8476-142576fa8877

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Quadratic small-jump bound for the Esscher Lévy drift correction. -/
theorem solution (φ z : ℝ) (hφ : 0 ≤ φ) (hz : 0 ≤ z) :
    z - z * Real.exp (-φ * z) ≤ φ * z ^ 2 := by
  have hlinear : 1 - Real.exp (-φ * z) ≤ φ * z := by
    have h := Real.add_one_le_exp (-φ * z)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlinear hz
  nlinarith
