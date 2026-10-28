-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:08:24.85216+00:00
-- url     : https://prove2.me/submissions/8d48427c-2055-4ff6-950d-77092066534c

import Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_all_negative_to_zero_Ioc_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_nonpos_eq_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    dividendMeasure (runningSup X) ω (Set.Iic (0 : ℝ)) = 0 := by
  exact AvramDividend.Classical.measure_Iic_zero_of_all_negative_to_zero_Ioc_zero _
    fun s hs => AvramDividend.Classical.runningSup_dividendMeasure_Ioc_nonpos_eq_zero X ω s 0 hs.le le_rfl
