-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb50_continuous_cutoff_stopped_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:38:53.288894+00:00
-- url     : https://prove2.me/submissions/25612f2e-f2e2-4110-b411-1bfc4d0009e2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/-- A continuous coefficient clipped to a Borel set and stopped at a
measurable clock is a measurable function of the original sample point. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Icc a b))
    (Y : Ω → ℝ) (hY : Measurable Y)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ)
    (t : ℝ≥0) (k : ℝ) :
    Measurable (fun ω => if t < ρ ω then
      k * (if Y ω ∈ Icc a b then f (Y ω) else 0) else 0) := by
  classical
  have hp : MeasurableSet {ω : Ω | t < ρ ω} :=
    (show MeasurableSet (Ioi t) from measurableSet_Ioi).preimage hρ
  have hc : Measurable (fun y : ℝ => if y ∈ Icc a b then f y else 0) := by
    exact hf.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  exact Measurable.ite hp (measurable_const.mul (hc.comp hY))
    measurable_const
