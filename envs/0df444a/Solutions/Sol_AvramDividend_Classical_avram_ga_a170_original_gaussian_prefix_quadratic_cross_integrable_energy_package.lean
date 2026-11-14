-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:09.077794+00:00
-- url     : https://prove2.me/submissions/3398e736-2c3e-41cf-a192-6e7edff6a14d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a172_nonnegative_lintegral_bound_integrable_real_expectation
import Theorems.Thm_AvramDividend_Classical_avram_ga_a176_original_gaussian_stopped_prefix_centered_square_measurable_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ga_a177_original_gaussian_true_stopped_source_real_energy_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a174_measurable_gaussian_quadratic_cross_integrable_of_centered_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped Gaussian prefix energy package via the source
quadratic ENNReal budget and finite-cross energy integrability transfer. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
    let A : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          |(Z m i ω + (Δ m : ℝ) * X.c)^2 - (Z m i ω)^2|
        else 0
    let E : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then (Z m i ω)^2 else 0
    (∀ m : ℕ, Integrable (A m) P) ∧
    (∀ m : ℕ, Integrable (E m) P) ∧
    (∀ m : ℕ, (∫ ω, E m ω ∂P) ≤ (n : ℝ) * X.σ^2) := by
  classical
  intro Δ Z A E
  letI : IsProbabilityMeasure P := X.isProbability
  have hρmeas : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hm (m i : ℕ) :
      MeasurableSet {ω : Ω | (i : ℝ≥0) * Δ m < ρ ω} := by
    have h : MeasurableSet
      {ω : Ω | (((i : ℝ≥0) * Δ m : ℝ≥0) : WithTop ℝ≥0) <
        (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ioi.preimage hρmeas
    simpa only [WithTop.coe_lt_coe] using h
  have hZm (m i : ℕ) : Measurable (Z m i) := by
    have h1 : Measurable (X.X ((i : ℝ≥0) * Δ m + Δ m)) :=
      (X.adapted ((i : ℝ≥0) * Δ m + Δ m)).mono (𝓕.le _) le_rfl
    have h0 : Measurable (X.X ((i : ℝ≥0) * Δ m)) :=
      (X.adapted ((i : ℝ≥0) * Δ m)).mono (𝓕.le _) le_rfl
    exact (h1.sub h0).sub measurable_const
  have hObs := avram_ga_a176_original_gaussian_stopped_prefix_centered_square_measurable_nonnegative
    X n ρ hρstop
  change ∀ m, Measurable (E m) ∧ ∀ ω, 0 ≤ E m ω at hObs
  have hB := avram_ga_a177_original_gaussian_true_stopped_source_real_energy_lintegral_bound
    X hNuZero n ρ
  change ∀ m, (∫⁻ ω, ENNReal.ofReal (E m ω) ∂P) ≤
    ENNReal.ofReal ((n : ℝ) * X.σ^2) at hB
  have hK : 0 ≤ (n : ℝ) * X.σ^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg X.σ)
  have hE (m : ℕ) :
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤
        (n : ℝ) * X.σ^2 :=
    avram_ga_a172_nonnegative_lintegral_bound_integrable_real_expectation
      P (E m) ((n : ℝ) * X.σ^2) (hObs m).1
      (Filter.Eventually.of_forall (hObs m).2) hK (hB m)
  have hAI (m : ℕ) : Integrable (A m) P := by
    have hCross := avram_ga_a174_measurable_gaussian_quadratic_cross_integrable_of_centered_energy
      P (Finset.range m) (fun i ω => (i : ℝ≥0) * Δ m < ρ ω)
      (hm m) (Z m) (hZm m) ((Δ m : ℝ) * X.c) (hE m).1
    exact hCross
  exact ⟨hAI, (fun m => (hE m).1), fun m => (hE m).2⟩
