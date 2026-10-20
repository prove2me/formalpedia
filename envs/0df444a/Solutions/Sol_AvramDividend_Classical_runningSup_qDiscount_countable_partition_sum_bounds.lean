-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_countable_partition_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:12:08.528366+00:00
-- url     : https://prove2.me/submissions/29fedd82-c055-4e8d-8526-7412b4527d02

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_countable_partition_sum_bounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (u : ℕ → ℝ) :
    (∑' i : ℕ,
        ENNReal.ofReal (Real.exp (-(q * u (i + 1)))) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) ≤
      (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∧
    (∑' i : ℕ,
        ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
      (∑' i : ℕ,
        ENNReal.ofReal (Real.exp (-(q * u i))) *
          ENNReal.ofReal
            (runningSup X (u (i + 1)).toNNReal ω -
             runningSup X (u i).toNNReal ω)) := by
  have hAnti :
      Antitone (fun r : ℝ =>
        ENNReal.ofReal (Real.exp (-(q * r)))) := by
    intro x y hxy
    have hMul : q * x ≤ q * y :=
      mul_le_mul_of_nonneg_left hxy hq
    have hNeg : -(q * y) ≤ -(q * x) := neg_le_neg hMul
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le hNeg)
  exact runningSup_discounted_countable_partition_sum_bounds
    X ω (fun r => ENNReal.ofReal (Real.exp (-(q * r)))) hAnti u
