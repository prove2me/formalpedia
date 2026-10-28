-- Prove2me | solution 2 for AvramDividend.Classical.firstRecord_capped_rightCont_stopping_and_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:48:20.931987+00:00
-- url     : https://prove2.me/submissions/a7e8d3b5-635f-4d7b-9c0c-9766ec7f2c3e

import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) :
    (let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     (∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) ∧
       Measurable τ) := by 
  exact ⟨firstRecord_truncation_stopping_rightCont X b N, firstRecord_truncation_clock_measurable X b N⟩
