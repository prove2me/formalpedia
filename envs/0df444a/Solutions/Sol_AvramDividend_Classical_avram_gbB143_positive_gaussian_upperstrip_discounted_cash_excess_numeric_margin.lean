-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB143_positive_gaussian_upperstrip_discounted_cash_excess_numeric_margin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:10:35.024269+00:00
-- url     : https://prove2.me/submissions/fc2c48ce-d3d2-4197-8f5d-8b75e74e5bb5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

theorem solution (G shape N : ℝ)
    (hG : (193419 / 96800 : ℝ) * (99999 / 100000 : ℝ) *
      (1 / 1000 : ℝ) ≤ G)
    (hShape : -(1 / 1936 : ℝ) ≤ shape)
    (hNoise : |N| ≤ (1 / 4000 : ℝ)) :
    (1 / 1000 : ℝ) ≤ G + shape + N := by
  have hN : -(1 / 4000 : ℝ) ≤ N := (abs_le.mp hNoise).1
  linarith
