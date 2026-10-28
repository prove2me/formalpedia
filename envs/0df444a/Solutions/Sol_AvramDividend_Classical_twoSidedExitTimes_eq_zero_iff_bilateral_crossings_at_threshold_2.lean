-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitTimes_eq_zero_iff_bilateral_crossings_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:13:27.285883+00:00
-- url     : https://prove2.me/submissions/bcb1e593-6982-426d-aac9-3f41cae4b82a

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    (twoSidedExitDownTime X b ω = 0 ∧ twoSidedExitUpTime X b ω = 0) ↔
      ((∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) ∧
       (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω)) := by 
  rw [twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold, twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold]
