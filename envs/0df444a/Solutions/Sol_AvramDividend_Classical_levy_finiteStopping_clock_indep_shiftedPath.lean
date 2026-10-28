-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_clock_indep_shiftedPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:36:42.100336+00:00
-- url     : https://prove2.me/submissions/df3ea6b7-2125-46a7-a01b-27f43ad1d7ff

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteStopping_clock_measurable_stoppedSigma
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedSigma_indep_shiftedPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A finite stopping clock is independent of the complete future Lévy increment path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    IndepFun τ
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) P := by
  classical
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hClock : Measurable[hstop.measurableSpace] τ := by
    simpa only [hstop] using
      (finiteStopping_clock_measurable_stoppedSigma τ hτ)
  have hSigma : Indep hstop.measurableSpace
      (MeasurableSpace.comap Y inferInstance) P := by
    simpa only [hstop, Y] using
      (levy_finiteStopping_stoppedSigma_indep_shiftedPath X τ hτ)
  have hSmall : MeasurableSpace.comap τ inferInstance ≤
      hstop.measurableSpace := hClock.comap_le
  exact (IndepFun_iff_Indep τ Y P).2
    (indep_of_indep_of_le_left hSigma hSmall)
