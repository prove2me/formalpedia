-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_lintegral_countable_interchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:21:19.666288+00:00
-- url     : https://prove2.me/submissions/0bf63067-6852-45ec-b149-46be74a7996e

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

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
    (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) :
    (∫⁻ r in paymentTimes τ,
      (∑' i : ℕ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0)
        ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
       ∫⁻ r in paymentTimes τ,
         if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) := by
  have hMeas (i : ℕ) :
      Measurable (fun r : ℝ =>
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0) := by
    exact Measurable.ite measurableSet_Ioc hw measurable_const
  exact MeasureTheory.lintegral_tsum (fun i => (hMeas i).aemeasurable)
