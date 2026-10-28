-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitUpTime_eq_zero_iff_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:20:05.775842+00:00
-- url     : https://prove2.me/submissions/8af57f91-272a-4fdc-a019-0ecd07ffc6f4

import Theorems.Thm_AvramDividend_Classical_positive_near_zero_of_twoSidedExitUpTime_zero
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    twoSidedExitUpTime X 0 ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by 
  exact ⟨positive_near_zero_of_twoSidedExitUpTime_zero X ω,
    twoSidedExitUpTime_eq_zero_of_positive_near_zero X ω⟩
