-- Prove2me | solution 1 for AvramDividend.Classical.levy_strongMarkov_shiftedPath_indep_stoppedEvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:46:59.36402+00:00
-- url     : https://prove2.me/submissions/7fe0f1e5-5dda-4381-bfc3-0e01bf037ba8

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_compl_event_adapted
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_mapLaw
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards
import Theorems.Thm_AvramDividend_Classical_restrictedMapLaw_event_marginal_factor
import Theorems.Thm_AvramDividend_Classical_indicator_indepFun_of_both_event_marginals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strong Markov independence of the whole post-stopping Lévy path and any stopped-past event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map
      (fun ω : Ω =>
        (Set.indicator A (fun _ : Ω => (1 : ℝ)) ω,
          fun t : ℝ≥0 => X.X (τ ω + t) ω - X.X (τ ω) ω)) P =
      (Measure.map (Set.indicator A (fun _ : Ω => (1 : ℝ))) P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hstop := isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hY : Measurable Y :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hRestricted (B : Set Ω)
      (hB : ∀ s : ℝ≥0,
        MeasurableSet[𝓕 s] (B ∩ {ω : Ω | τ ω ≤ s})) :
      Measure.map Y (P.restrict B) = (P B) • Measure.map Z P := by
    have hMass : (Measure.map Y (P.restrict B)) Set.univ ≠ ⊤ := by
      rw [Measure.map_apply hY MeasurableSet.univ]
      exact measure_ne_top (P.restrict B) Set.univ
    apply scaled_piPathMeasure_eq_of_finite_pushforwards
      Y Z hY hZ (P B) hMass
    intro J
    simpa only [Y, Z] using
      (levy_finiteStopping_restrictedFDD_mapLaw X τ hstop B hB J)
  have hSet : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  have hCompl := stoppedHistory_compl_event_adapted τ hτ A hA
  have hUniv : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Set.univ ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    simpa only [Set.univ_inter] using hτ s
  have hFull : Measure.map Y P = Measure.map Z P := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using
      (hRestricted Set.univ hUniv)
  have hLawA : Measure.map Y (P.restrict A) =
      (P A) • Measure.map Y P := by
    rw [hRestricted A hA, hFull]
  have hLawCompl : Measure.map Y (P.restrict Aᶜ) =
      (P Aᶜ) • Measure.map Y P := by
    rw [hRestricted Aᶜ hCompl, hFull]
  have hFirst : ∀ B : Set (ℝ≥0 → ℝ), MeasurableSet B →
      P (A ∩ Y ⁻¹' B) = P A * P (Y ⁻¹' B) := by
    intro B hB
    exact restrictedMapLaw_event_marginal_factor P Y hY A hLawA B hB
  have hSecond : ∀ B : Set (ℝ≥0 → ℝ), MeasurableSet B →
      P (Aᶜ ∩ Y ⁻¹' B) = P Aᶜ * P (Y ⁻¹' B) := by
    intro B hB
    exact restrictedMapLaw_event_marginal_factor P Y hY Aᶜ hLawCompl B hB
  have hIndep :=
    indicator_indepFun_of_both_event_marginals
      A Y hSet hY hFirst hSecond
  have hInd : Measurable (Set.indicator A (fun _ : Ω => (1 : ℝ))) :=
    measurable_const.indicator hSet
  have hProd :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hInd.aemeasurable hY.aemeasurable).1 hIndep
  rw [hFull] at hProd
  simpa only [Y, Z] using hProd
