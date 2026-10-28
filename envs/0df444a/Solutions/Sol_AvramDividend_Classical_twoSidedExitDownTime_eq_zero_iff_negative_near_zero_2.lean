-- Prove2me | solution 2 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_iff_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:20:05.281374+00:00
-- url     : https://prove2.me/submissions/acdd6e3d-edce-4fed-9010-5f5a1cfb8ce5

import Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    twoSidedExitDownTime X 0 ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by 
  exact ⟨negative_near_zero_of_twoSidedExitDownTime_zero X ω,
    twoSidedExitDownTime_eq_zero_of_negative_near_zero X ω⟩
