-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Iic_zero_of_monotone_rightLim
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:10:41.487004+00:00
-- url     : https://prove2.me/submissions/86159313-241c-4a1d-a85f-8347ee7d1784

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim
import Theorems.Thm_AvramDividend_Classical_measure_Iic_zero_of_all_negative_to_zero_Ioc_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hm : Monotone (fun r : ℝ => D r.toNNReal ω))
    (hr : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => D v.toNNReal ω) r =
        D r.toNNReal ω) :
    (dividendMeasure D ω) (Set.Iic (0 : ℝ)) = 0 := by
  refine AvramDividend.Classical.measure_Iic_zero_of_all_negative_to_zero_Ioc_zero _ fun s hs => ?_
  rw [AvramDividend.Classical.dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim D ω s 0 hm hr,
    Real.toNNReal_of_nonpos hs.le, Real.toNNReal_zero, sub_self, ENNReal.ofReal_zero]
