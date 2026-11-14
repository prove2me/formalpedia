-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB312_scaled_translated_gaussian_open_cell_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:14:12.384917+00:00
-- url     : https://prove2.me/submissions/b086e597-7544-40be-a88b-1600c059c249

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB309_translated_inverse_sqrt_open_cell_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB310_translated_inverse_sqrt_cell_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Scaling the translated Gaussian time-kernel bound by any nonnegative extended-real constant. -/
theorem solution (s δ : ℝ) (hδ : 0 ≤ δ) (C : ℝ≥0∞) :
    (∫⁻ t in Set.Ioo s (s + δ),
      C * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume) ≤
      C * ENNReal.ofReal (2 * Real.sqrt δ) := by
  have hf :=
    avram_gbB310_translated_inverse_sqrt_cell_integrable s δ hδ
  have h := avram_gbB309_translated_inverse_sqrt_open_cell_lintegral_bound
    s δ hδ hf
  calc
    (∫⁻ t in Set.Ioo s (s + δ),
      C * ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume) =
        C * (∫⁻ t in Set.Ioo s (s + δ),
          ENNReal.ofReal ((t - s) ^ (-(1 / 2 : ℝ))) ∂volume) := by
            rw [lintegral_const_mul]
            all_goals measurability
    _ ≤ C * ENNReal.ofReal (2 * Real.sqrt δ) :=
      mul_le_mul_of_nonneg_left h (by positivity)
