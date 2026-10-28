-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_stoppedSigma_indep_shiftedPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:21:51.394988+00:00
-- url     : https://prove2.me/submissions/5feec84c-fbd5-4944-adfc-bc864a3e60dd

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_restrictedMapLaw_event_marginal_factor
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A finite stopping time's stopped history is independent of the entire future increment path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        inferInstance) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hY : Measurable Y :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  have hUniv : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Set.univ ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    simpa only [Set.univ_inter] using hτ s
  have hFull : Measure.map Y P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
    simpa only [Y, Measure.restrict_univ, measure_univ, one_smul] using
      (levy_finiteStopping_restrictedFuturePath_mapLaw
        X τ hstop Set.univ hUniv)
  change Indep hstop.measurableSpace
    (MeasurableSpace.comap Y inferInstance) P
  apply (indep_iff_forall_indepSet P).2
  intro A B hA hB
  obtain ⟨T, hT, hBT⟩ := (MeasurableSpace.measurableSet_comap).mp hB
  subst B
  have hAstopped : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    have hs := ((hstop.measurableSet A).mp hA).2 s
    simpa only [WithTop.coe_le_coe] using hs
  have hAmbient : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hAstopped
  have hLaw : Measure.map Y (P.restrict A) =
      (P A) • Measure.map Y P := by
    have hOriginal :=
      levy_finiteStopping_restrictedFuturePath_mapLaw
        X τ hstop A hAstopped
    rw [← hFull] at hOriginal
    simpa only [Y] using hOriginal
  have hFactor : P (A ∩ Y ⁻¹' T) = P A * P (Y ⁻¹' T) :=
    restrictedMapLaw_event_marginal_factor P Y hY A hLaw T hT
  exact (indepSet_iff_measure_inter_eq_mul
    hAmbient (hY hT) P).2 hFactor
