-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_restricted_real_deficit_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:46:21.062215+00:00
-- url     : https://prove2.me/submissions/213c312e-92b9-4334-9a55-3bc2ac6fc3d2

import Theorems.Thm_AvramDividend_Classical_negative_levy_real_exponential_deficit_tendsto_atTop
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Infinite negative jump activity forces divergence on the strictly negative band. -/
theorem solution
    (ν : Measure ℝ)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (hInt : ∀ n : ℕ, Integrable
      (fun y : ℝ => 1 - Real.exp ((n : ℝ) * y))
      (ν.restrict (Iio (0 : ℝ)))) :
    Tendsto
      (fun n : ℕ => ∫ y in Iio (0 : ℝ),
        (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop atTop := by 
  refine negative_levy_real_exponential_deficit_tendsto_atTop (ν.restrict (Iio 0)) ?_ ?_ hInt
  · rw [Measure.restrict_apply measurableSet_Ici]
    convert measure_empty (μ := ν)
    ext y; simp
  · rw [Measure.restrict_apply measurableSet_Iio, inter_self, hνinf]
