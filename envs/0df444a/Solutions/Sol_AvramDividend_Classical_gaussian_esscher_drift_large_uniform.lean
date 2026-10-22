-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_drift_large_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:21:21.361899+00:00
-- url     : https://prove2.me/submissions/86138d92-173e-4daa-b1d6-1c1b98d3f371

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Uniform large-jump bound on the damped Lévy drift correction. -/
theorem solution (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    z * Real.exp (-φ * z) ≤ 1 / φ := by
  have hlinear : φ * z ≤ Real.exp (φ * z) := by
    have h := Real.add_one_le_exp (φ * z)
    linarith
  have hproduct : Real.exp (φ * z) * Real.exp (-φ * z) = 1 := by
    rw [← Real.exp_add]
    simp
  have hb : φ * z * Real.exp (-φ * z) ≤ 1 := by
    calc
      _ ≤ Real.exp (φ * z) * Real.exp (-φ * z) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
      _ = 1 := hproduct
  apply (le_div_iff₀ hφ).2
  nlinarith
