-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_thresholdEvent_indep_shiftedPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:13:35.519237+00:00
-- url     : https://prove2.me/submissions/99bb301b-3d4c-419e-b282-b7e2fe2d2867

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_strongMarkov_shiftedPath_indep_stoppedEvent
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every stopping-clock threshold indicator is independent of the full shifted future Lévy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (c : ℝ≥0) :
    IndepFun
      (Set.indicator {ω : Ω | τ ω ≤ c} (fun _ : Ω => (1 : ℝ)))
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Set Ω := {ω : Ω | τ ω ≤ c}
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    have heq : A ∩ {ω : Ω | τ ω ≤ s} =
        {ω : Ω | τ ω ≤ min c s} := by
      ext ω
      simp only [A, Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff]
    rw [heq]
    exact (𝓕.mono (min_le_right c s)) _ (hτ (min c s))
  have hSet : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  have hIndicator : Measurable
      (Set.indicator A (fun _ : Ω => (1 : ℝ))) :=
    measurable_const.indicator hSet
  have hY : Measurable Y :=
    levy_finiteStopping_stoppedFuturePath_measurable
      X τ (isStoppingTime_withTop_of_le_events τ hτ)
  have hProduct :=
    levy_strongMarkov_shiftedPath_indep_stoppedEvent X τ hτ A hA
  have hUniv : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Set.univ ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    simpa only [Set.univ_inter] using hτ s
  have hFull : Measure.map Y P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
    simpa only [Y, Measure.restrict_univ, measure_univ, one_smul] using
      (levy_finiteStopping_restrictedFuturePath_mapLaw
        X τ (isStoppingTime_withTop_of_le_events τ hτ) Set.univ hUniv)
  rw [← hFull] at hProduct
  have hInd :
      IndepFun (Set.indicator A (fun _ : Ω => (1 : ℝ))) Y P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      hIndicator.aemeasurable hY.aemeasurable).2
    simpa only [Y] using hProduct
  simpa only [A, Y] using hInd
