-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_full_future_conditional_strong_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:47:02.076595+00:00
-- url     : https://prove2.me/submissions/7c1e2e1f-60c0-42e8-bcae-20497017d06f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_full_future_source_law
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_future_functional_condExp
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (Z : (ℝ≥0 → ℝ) → ℝ) (hZmeas : Measurable Z)
    (hInt : Integrable (fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) P) :
    P[(fun ω : Ω => Z (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => ∫ ω, Z (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  obtain ⟨Y, hYpath, -, -, -⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  let R : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hRmeas : Measurable R := by
    simpa only [R, hYpath] using
      (levy_finiteStopping_stoppedFuturePath_measurable Y τ hτstop)
  have hXmeas :
      Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) :=
    levy_wholePath_measurable X
  have hLaw :
      Measure.map R P =
        Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
    simpa only [R] using
      (avram_wave6_03_original_rightCont_stopped_full_future_source_law
        X τ hτ)
  have hIntegralLaw :
      (∫ ω, Z (R ω) ∂P) =
        (∫ ω, Z (fun t : ℝ≥0 => X.X t ω) ∂P) := by
    calc
      (∫ ω, Z (R ω) ∂P) =
          ∫ r, Z r ∂(Measure.map R P) :=
        (integral_map hRmeas.aemeasurable
          hZmeas.stronglyMeasurable.aestronglyMeasurable).symm
      _ = ∫ r, Z r ∂(Measure.map
            (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
        rw [hLaw]
      _ = ∫ ω, Z (fun t : ℝ≥0 => X.X t ω) ∂P :=
        integral_map hXmeas.aemeasurable
          hZmeas.stronglyMeasurable.aestronglyMeasurable
  have hCE :=
    avram_wave6_03_original_rightCont_stopped_future_functional_condExp
      X τ hτ Z hZmeas hInt
  change P[(fun ω => Z (R ω)) | hτstop.measurableSpace] =ᵐ[P]
    (fun _ => ∫ ω, Z (fun t : ℝ≥0 => X.X t ω) ∂P)
  change P[(fun ω => Z (R ω)) | hτstop.measurableSpace] =ᵐ[P]
    (fun _ => ∫ ω, Z (R ω) ∂P) at hCE
  simpa only [hIntegralLaw] using hCE
