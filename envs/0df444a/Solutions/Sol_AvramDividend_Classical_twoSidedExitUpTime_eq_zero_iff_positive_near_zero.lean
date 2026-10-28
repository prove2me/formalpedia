-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitUpTime_eq_zero_iff_positive_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:19:30.449059+00:00
-- url     : https://prove2.me/submissions/41d4b444-50e1-4d2d-a5d0-0832a9f11ddf

import Theorems.Thm_AvramDividend_Classical_positive_near_zero_of_twoSidedExitUpTime_zero
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_of_positive_near_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero-time strict exit is equivalent to arbitrary near-zero strict crossings. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    twoSidedExitUpTime X 0 ω = 0 ↔
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω := by
  constructor
  · exact positive_near_zero_of_twoSidedExitUpTime_zero X ω
  · exact twoSidedExitUpTime_eq_zero_of_positive_near_zero X ω
