-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_expected_survived_interval_record_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:43:13.040418+00:00
-- url     : https://prove2.me/submissions/d457c081-360e-4d0b-9553-569de7febe9d

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_discount_record_bounds_of_survival
import Mathlib.Analysis.Complex.Exponential

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
            (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) else 0 ∂P) ≤
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
             if r ∈ Set.Ioc s t then
               ENNReal.ofReal (Real.exp (-(q * r))) else 0
             ∂(dividendMeasure (runningSup X) ω) else 0 ∂P) ∧
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
             if r ∈ Set.Ioc s t then
               ENNReal.ofReal (Real.exp (-(q * r))) else 0
             ∂(dividendMeasure (runningSup X) ω) else 0 ∂P) ≤
    (∫⁻ ω, if ENNReal.ofReal t < barrierRuinTime X a ω
       then ENNReal.ofReal (Real.exp (-(q * s))) *
         ENNReal.ofReal
            (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) else 0 ∂P) := by
  classical
  have hBound (ω : Ω)
      (ht : ENNReal.ofReal t < barrierRuinTime X a ω) :=
    runningSup_stopped_Ioc_discount_record_bounds_of_survival
      X ω (barrierRuinTime X a ω) q hq s t
      (paymentTimes_Ioc_subset_of_terminal_survival
        (barrierRuinTime X a ω) s t hs ht)
  constructor
  · apply lintegral_mono
    intro ω
    by_cases ht : ENNReal.ofReal t < barrierRuinTime X a ω
    · simpa only [if_pos ht] using (hBound ω ht).1
    · simp only [if_neg ht, le_refl]
  · apply lintegral_mono
    intro ω
    by_cases ht : ENNReal.ofReal t < barrierRuinTime X a ω
    · simpa only [if_pos ht] using (hBound ω ht).2
    · simp only [if_neg ht, le_refl]
