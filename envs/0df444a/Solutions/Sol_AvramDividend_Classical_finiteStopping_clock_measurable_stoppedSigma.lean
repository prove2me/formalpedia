-- Prove2me | solution 1 for AvramDividend.Classical.finiteStopping_clock_measurable_stoppedSigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:23:14.138004+00:00
-- url     : https://prove2.me/submissions/fa6fbe33-4900-47d6-a3dd-bdefc1609bd7

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_threshold_event_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every finite stopping clock is measurable against its stopped-history sigma-algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] τ := by
  classical
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  change Measurable[hstop.measurableSpace] τ
  apply measurable_of_Iic
  intro c
  change MeasurableSet[hstop.measurableSpace] {ω : Ω | τ ω ≤ c}
  have hA :=
    finiteStopping_threshold_event_stoppedHistory τ hτ c
  have hAtSup : MeasurableSet[(⨆ t, 𝓕 t)] {ω : Ω | τ ω ≤ c} :=
    (le_iSup (fun t => 𝓕 t) c) _ (hτ c)
  have hWithTop : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        ({ω : Ω | τ ω ≤ c} ∩
          {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}) := by
    intro s
    simpa only [WithTop.coe_le_coe] using hA s
  exact (hstop.measurableSet _).2 ⟨hAtSup, hWithTop⟩
