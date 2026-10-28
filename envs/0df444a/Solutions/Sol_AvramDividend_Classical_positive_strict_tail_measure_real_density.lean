-- Prove2me | solution 1 for AvramDividend.Classical.positive_strict_tail_measure_real_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:45:51.946266+00:00
-- url     : https://prove2.me/submissions/2eb9441f-aba9-424c-b301-35ec8f50e5ab

import Theorems.Thm_AvramDividend_Classical_positive_tail_finite_of_finite_first_moment
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ≥0)
    (hmoment : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t : ℝ => μ {z : ℝ≥0 | t < (z : ℝ)}) =
    volume.withDensity
      (fun t : ℝ =>
        ENNReal.ofReal (if 0 < t then
          (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal else 0)) := by
  have hfin := positive_tail_finite_of_finite_first_moment μ hmoment
  rw [← withDensity_indicator measurableSet_Ioi]
  congr 1
  funext t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht), if_pos ht, ENNReal.ofReal_toReal (hfin t ht)]
  · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht), if_neg ht, ENNReal.ofReal_zero]
