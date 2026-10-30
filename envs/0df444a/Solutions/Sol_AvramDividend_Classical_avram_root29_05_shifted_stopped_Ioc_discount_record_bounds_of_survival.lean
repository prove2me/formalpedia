-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_stopped_Ioc_discount_record_bounds_of_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:43:10.426053+00:00
-- url     : https://prove2.me/submissions/c2964363-8f5f-42f8-8587-b359a74d18bd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_lintegral_indicator_restrict_of_subset
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_qDiscount_Ioc_record_bounds
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Stopping removes no shifted Stieltjes dividend cash from a time interval
known entirely to precede the shifted strict-ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ)
    (hSurvive : Ioc s t ⊆ paymentTimes τ) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal) ≤
      ∫⁻ r in paymentTimes τ,
        if r ∈ Ioc s t then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ∧
    ((∫⁻ r in paymentTimes τ,
        if r ∈ Ioc s t then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal)) := by
  classical
  let M : ℝ≥0 → ℝ := fun v =>
    sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
  let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
  let w : ℝ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (Real.exp (-(q * r)))
  have hRaw := lintegral_indicator_restrict_of_subset μ
    (paymentTimes τ) (Ioc s t)
    (paymentTimes_measurable τ) measurableSet_Ioc hSurvive w
  have hEq :
      (∫⁻ r in paymentTimes τ,
        if r ∈ Ioc s t then w r else 0 ∂μ) =
      (∫⁻ r, if r ∈ Ioc s t then w r else 0 ∂μ) := by
    calc
      _ = (∫⁻ r in paymentTimes τ,
            (Ioc s t).indicator w r ∂μ) := by
              apply lintegral_congr
              intro r
              by_cases hr : r ∈ Ioc s t <;> simp [hr]
      _ = (∫⁻ r, (Ioc s t).indicator w r ∂μ) := hRaw
      _ = _ := by
          apply lintegral_congr
          intro r
          by_cases hr : r ∈ Ioc s t <;> simp [hr]
  change (w t * ENNReal.ofReal (M t.toNNReal - M s.toNNReal) ≤
    ∫⁻ r in paymentTimes τ, if r ∈ Ioc s t then w r else 0 ∂μ) ∧
    ((∫⁻ r in paymentTimes τ, if r ∈ Ioc s t then w r else 0 ∂μ) ≤
      w s * ENNReal.ofReal (M t.toNNReal - M s.toNNReal))
  rw [hEq]
  exact avram_root29_05_shifted_qDiscount_Ioc_record_bounds
    X ω age q hq s t
