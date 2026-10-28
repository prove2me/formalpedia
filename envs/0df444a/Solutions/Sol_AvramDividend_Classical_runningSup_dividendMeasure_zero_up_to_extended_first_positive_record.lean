-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_zero_up_to_extended_first_positive_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:18:38.214715+00:00
-- url     : https://prove2.me/submissions/9b104dc9-70f7-41b8-961b-3a05337fe1b8

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_before_extended_first_positive_record
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_through_first_positive_record

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc (0 : ℝ) (t : ℝ)) = 0 := by
  rcases eq_or_lt_of_le ht with heq | hlt
  · apply runningSup_dividendMeasure_zero_through_first_positive_record
      X 0 (by exact le_refl 0) ω t
    exact heq
  · exact runningSup_dividendMeasure_zero_before_extended_first_positive_record
      X ω t hlt
