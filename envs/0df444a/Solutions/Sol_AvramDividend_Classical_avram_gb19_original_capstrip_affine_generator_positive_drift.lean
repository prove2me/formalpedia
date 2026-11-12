-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb19_original_capstrip_affine_generator_positive_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:34:47.624996+00:00
-- url     : https://prove2.me/submissions/080e3809-1726-4841-94b7-56a1285e83af

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (c q wb b y : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ wb) (hby : b ≤ y) :
    c - q * (wb + (y - b)) ≤ max c 0 := by
  have hlinear : 0 ≤ wb + (y - b) := by linarith
  have hdiscount : 0 ≤ q * (wb + (y - b)) := mul_nonneg hq hlinear
  have hc : c ≤ max c 0 := le_max_left _ _
  linarith
