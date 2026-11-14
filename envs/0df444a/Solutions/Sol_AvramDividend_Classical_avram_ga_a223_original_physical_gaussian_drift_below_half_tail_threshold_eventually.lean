-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a223_original_physical_gaussian_drift_below_half_tail_threshold_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T01:01:10.557071+00:00
-- url     : https://prove2.me/submissions/927c873b-03c9-45d8-9509-65adc7c18964

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (n : ℕ) (c δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      |(((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * c| ≤
        δ / 2 := by
  have hw : Tendsto (fun m : ℕ =>
      (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    exact NNReal.tendsto_coe.mpr
      (avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero (n : ℝ≥0))
  have hlim : Tendsto (fun m : ℕ =>
      |(((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * c|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hw.mul_const c).abs
  have hs : (0 : ℝ) < δ / 2 := by linarith
  have hev : ∀ᶠ m : ℕ in atTop,
      |(((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * c| <
        δ / 2 :=
    hlim.eventually (isOpen_Iio.mem_nhds hs)
  exact hev.mono (fun m h => le_of_lt h)
