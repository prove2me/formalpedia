-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_two_noise_mesh_squared_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:45:57.179759+00:00
-- url     : https://prove2.me/submissions/eb57b2d7-ca94-4d12-92b9-886129ae5e5d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
/-- Universal deterministic L2 energy bound for two Gaussian grid noise channels. -/
theorem solution
    (a b c d : ℝ) :
    ((a + c) - (b + d)) ^ 2 ≤
      2 * (a - b) ^ 2 + 4 * c ^ 2 + 4 * d ^ 2 := by
  nlinarith [sq_nonneg ((a - b) - (c - d)),
    sq_nonneg (c + d)]
