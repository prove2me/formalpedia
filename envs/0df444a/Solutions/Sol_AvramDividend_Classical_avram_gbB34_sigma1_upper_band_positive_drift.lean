-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB34_sigma1_upper_band_positive_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:16:51.112903+00:00
-- url     : https://prove2.me/submissions/19f9a7d5-cfb8-4f89-9fe5-2fa9b6b802d3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution (y : ℝ) (hylo : (5 / 44 : ℝ) ≤ y)
  (hyhi : y ≤ (1 / 8 : ℝ)) :
  (193419 / 96800 : ℝ) ≤ 2 - (1 / 100 : ℝ) * (y + 15 / 242) ∧
  0 ≤ y - 4 * y ^ 2 - 15 / 242 ∧
  y - 4 * y ^ 2 - 15 / 242 ≤ (1 / 1936 : ℝ) := by
  have hlower : 0 ≤ (y - (5 / 44 : ℝ)) * ((3 / 22 : ℝ) - y) :=
    mul_nonneg (by linarith) (by linarith)
  have hupper : 0 ≤ ((1 / 8 : ℝ) - y) * ((1 / 2 : ℝ) - 4 * y) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · nlinarith
  constructor
  · nlinarith [hlower]
  · nlinarith [hupper]
