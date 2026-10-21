-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_ge_survived_interval_discounted_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:04:28.176979+00:00
-- url     : https://prove2.me/submissions/edc9aab5-4ead-413e-89b7-213bbd662516

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_full_reward_indicator_expectation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q s t : ℝ)
    (hq : 0 ≤ q) (hs : 0 ≤ s) :
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ENNReal.ofReal (Real.exp (-(q * t))) *
         ENNReal.ofReal
           (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)
       else 0 ∂P) ≤ barrierSupValue X a q := by
  classical
  rw [barrierSupValue_eq_full_reward_indicator_expectation X a q]
  apply lintegral_mono
  intro ω
  let τ := barrierRuinTime X a ω
  let μ := dividendMeasure (runningSup X) ω
  let w : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  by_cases ht : ENNReal.ofReal t < τ
  · have hpay : Set.Ioc s t ⊆ paymentTimes τ :=
      paymentTimes_Ioc_subset_of_terminal_survival τ s t hs ht
    have hlower := (runningSup_stopped_Ioc_discount_record_bounds_of_survival
      X ω τ q hq s t hpay).1
    have hmono :
        (∫⁻ r in paymentTimes τ, if r ∈ Set.Ioc s t then w r else 0 ∂μ) ≤
        (∫⁻ r in paymentTimes τ, w r ∂μ) := by
      apply lintegral_mono
      intro r
      by_cases hr : r ∈ Set.Ioc s t
      · simp [hr]
      · simp [hr]
    have hFull :
        (∫⁻ r in paymentTimes τ, w r ∂μ) =
        (∫⁻ r, if r ∈ paymentTimes τ then w r else 0 ∂μ) := by
      change (∫⁻ r in paymentTimes τ, w r ∂μ) =
        (∫⁻ r, (paymentTimes τ).indicator w r ∂μ)
      exact (lintegral_indicator
        (μ := μ) (paymentTimes_measurable τ) w).symm
    calc
      (if ENNReal.ofReal t < τ then
         ENNReal.ofReal (Real.exp (-(q * t))) *
           ENNReal.ofReal
             (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)
         else 0) =
        ENNReal.ofReal (Real.exp (-(q * t))) *
          ENNReal.ofReal
            (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) := by
              simp [ht]
      _ ≤ (∫⁻ r in paymentTimes τ,
              if r ∈ Set.Ioc s t then w r else 0 ∂μ) := hlower
      _ ≤ (∫⁻ r in paymentTimes τ, w r ∂μ) := hmono
      _ = (∫⁻ r, if r ∈ paymentTimes τ then w r else 0 ∂μ) := hFull
  · have hneg :
        ¬ ENNReal.ofReal t < barrierRuinTime X a ω := ht
    change
      (if ENNReal.ofReal t < barrierRuinTime X a ω
       then ENNReal.ofReal (Real.exp (-(q * t))) *
         ENNReal.ofReal
           (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)
       else 0) ≤
      (∫⁻ r, if r ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω))
    rw [if_neg hneg]
    exact bot_le
