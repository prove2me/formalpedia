-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_dividendMeasure_zero_up_to_extended_first_positive_record
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:19:21.500296+00:00
-- url     : https://prove2.me/submissions/15abd1f3-48e3-4e08-8324-22c6c5dc850c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_before_extended_first_positive_record
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_through_first_positive_record

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc (0 : ℝ) (t : ℝ)) = 0 := by
  rcases ht.lt_or_eq with h | h
  · exact runningSup_dividendMeasure_zero_before_extended_first_positive_record X ω t h
  · exact runningSup_dividendMeasure_zero_through_first_positive_record X 0 le_rfl ω t h
