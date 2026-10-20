-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_interval_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:20:22.069403+00:00
-- url     : https://prove2.me/submissions/a46bc9eb-8457-4554-9699-554a38081324

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (s t : ℝ) :
    ((∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0
        ∂(dividendMeasure (runningSup X) ω))) := by
  have hAnti :
      Antitone (fun r : ℝ =>
        ENNReal.ofReal (Real.exp (-(q * r)))) := by
    intro x y hxy
    have hMul : q * x ≤ q * y :=
      mul_le_mul_of_nonneg_left hxy hq
    have hNeg : -(q * y) ≤ -(q * x) := neg_le_neg hMul
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le hNeg)
  exact runningSup_discounted_interval_weight_bounds
    X ω (fun r => ENNReal.ofReal (Real.exp (-(q * r))))
    hAnti s t
