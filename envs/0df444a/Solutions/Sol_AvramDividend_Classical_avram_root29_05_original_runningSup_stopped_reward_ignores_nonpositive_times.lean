-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_original_runningSup_stopped_reward_ignores_nonpositive_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:08:17.313983+00:00
-- url     : https://prove2.me/submissions/af56b81c-5a4d-4839-acd8-5310c39c1167

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- On every actual Lévy path the original running-supremum regulator's
dividend Stieltjes measure has zero mass at all nonpositive times, so a
strict positive-time cash filter leaves any stopped dividend reward unchanged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  have hAe : ∀ᵐ r : ℝ ∂μ, 0 < r := by
    apply ae_iff.mpr
    have hset : ({r : ℝ | ¬0 < r}) = Set.Iic 0 := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Iic, not_lt]
    rw [hset]
    exact runningSup_dividendMeasure_zero_nonpositive X ω
  rw [← lintegral_indicator (paymentTimes_measurable τ),
      ← lintegral_indicator (paymentTimes_measurable τ)]
  apply lintegral_congr_ae
  filter_upwards [hAe] with r hr
  by_cases hp : r ∈ paymentTimes τ
  · simp [Set.indicator, hp, hr]
  · simp [Set.indicator, hp]
