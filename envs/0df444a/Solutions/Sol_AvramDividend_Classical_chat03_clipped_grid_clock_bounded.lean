-- Prove2me | solution 1 for AvramDividend.Classical.chat03_clipped_grid_clock_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:31:14.033203+00:00
-- url     : https://prove2.me/submissions/6fdf9ef9-ca14-4267-979b-878570544751

import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-!
A uniform-grid clock clipped at a nonnegative physical horizon is
monotone, starts at zero and remains below the horizon, even if the
terminal ceiling-grid step exceeds that horizon.
-/
theorem solution
    (T h : ℝ≥0) :
    Monotone (fun j : ℕ => min ((j : ℝ≥0) * h) T) ∧
    (min ((0 : ℝ≥0) * h) T = 0) ∧
    (∀ j : ℕ, min ((j : ℝ≥0) * h) T ≤ T) := by
  constructor
  · intro i j hij
    have hcast : (i : ℝ≥0) ≤ (j : ℝ≥0) := by
      exact_mod_cast hij
    exact min_le_min
      (mul_le_mul_of_nonneg_right hcast (show 0 ≤ h from zero_le)) le_rfl
  constructor
  · simp
  · intro j
    exact min_le_right _ _
