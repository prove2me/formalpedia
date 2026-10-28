-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_zero_before_extended_first_positive_record
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:11:53.738894+00:00
-- url     : https://prove2.me/submissions/98be89fa-115d-41d0-a9e4-edec8fe3e182

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_extended_upcrossing_clock_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) <
      (⨅ (r : ℝ≥0) (_ : 0 < X.X r ω), (r : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω) (Set.Ioc (0 : ℝ) (t : ℝ)) = 0 := by
  rw [AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_record_increment, ENNReal.ofReal_eq_zero,
    Real.toNNReal_coe]
  have h1 := AvramDividend.Classical.runningSup_pre_extended_upcrossing_clock_le X ω 0 t ht
  have h2 := (AvramDividend.Classical.runningSup_eq_rawSup_nonneg X (0 : ℝ).toNNReal ω).2
  linarith
