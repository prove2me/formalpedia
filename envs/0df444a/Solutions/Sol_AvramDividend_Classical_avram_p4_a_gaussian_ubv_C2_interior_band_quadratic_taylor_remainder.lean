-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_interior_band_quadratic_taylor_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:01:05.603754+00:00
-- url     : https://prove2.me/submissions/e2dc797c-ded8-422c-adc8-f83982f7af52

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict interior C² gives a compact first-order Taylor remainder of
quadratic order, without endpoint or global smoothness assumptions. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, ∀ y ∈ Icc a b,
      ‖w y - taylorWithinEval w 1 (Icc a b) a y‖ ≤
        K * (y - a) ^ 2 := by
  have hwBand : ContDiffOn ℝ (1 + 1) w (Icc a b) := by
    simpa only [one_add_one_eq_two] using hwC2.mono hBand
  exact exists_taylor_mean_remainder_bound hab hwBand
