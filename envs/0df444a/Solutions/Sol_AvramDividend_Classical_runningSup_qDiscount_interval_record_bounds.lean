-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_interval_record_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:40:15.147913+00:00
-- url     : https://prove2.me/submissions/b719d500-6122-4256-8004-4be129673eb5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

 /- The actual q-discounted regulator interval reward, expressed in record increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (s t : ℝ) :
    (ENNReal.ofReal (Real.exp (-(q * t))) *
       ENNReal.ofReal
         (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) ≤
      ∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)) := by
  have hAnti :
      Antitone (fun r : ℝ =>
        ENNReal.ofReal (Real.exp (-(q * r)))) := by
    intro x y hxy
    have hMul : q * x ≤ q * y :=
      mul_le_mul_of_nonneg_left hxy hq
    have hNeg : -(q * y) ≤ -(q * x) := neg_le_neg hMul
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le hNeg)
  exact runningSup_discounted_interval_bounds_record_increment
    X ω (fun r => ENNReal.ofReal (Real.exp (-(q * r)))) hAnti s t
