-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_Ioc_discount_record_bounds_of_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:43:10.621628+00:00
-- url     : https://prove2.me/submissions/cb53e0d5-165f-4e71-b1a0-9ed60868dacd

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_lintegral_indicator_restrict_of_subset
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_interval_record_bounds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ)
    (hSurvive : Set.Ioc s t ⊆ paymentTimes τ) :
    (ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)) := by
  classical
  let μ := dividendMeasure (runningSup X) ω
  let w : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  have hRaw := lintegral_indicator_restrict_of_subset μ
    (paymentTimes τ) (Set.Ioc s t)
    (paymentTimes_measurable τ) measurableSet_Ioc hSurvive w
  have hEq :
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc s t then w r else 0 ∂μ) =
      (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0 ∂μ) := by
    calc
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc s t then w r else 0 ∂μ) =
        (∫⁻ r in paymentTimes τ,
          (Set.Ioc s t).indicator w r ∂μ) := by
            apply lintegral_congr
            intro r
            by_cases hr : r ∈ Set.Ioc s t
            · simp [hr]
            · simp [hr]
      _ = (∫⁻ r, (Set.Ioc s t).indicator w r ∂μ) := by
            exact hRaw
      _ = (∫⁻ r, if r ∈ Set.Ioc s t then w r else 0 ∂μ) := by
            apply lintegral_congr
            intro r
            by_cases hr : r ∈ Set.Ioc s t
            · simp [hr]
            · simp [hr]
  rw [hEq]
  exact runningSup_qDiscount_interval_record_bounds X ω q hq s t
