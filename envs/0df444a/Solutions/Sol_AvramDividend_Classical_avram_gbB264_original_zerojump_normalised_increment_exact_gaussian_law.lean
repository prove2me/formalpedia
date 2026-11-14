-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB264_original_zerojump_normalised_increment_exact_gaussian_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:51:16.846195+00:00
-- url     : https://prove2.me/submissions/3e091e2e-46fb-483e-81bc-ca1469822d00

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive-ray moment generating functions identify a Gaussian pushforward law. -/
private theorem gaussianLaw_of_positiveMGF
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (m : ℝ) (v : ℝ≥0)
    (hInt : ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMGF : ∀ θ : ℝ, 0 < θ →
      mgf Z P θ = mgf id (gaussianReal m v) θ) :
    Measure.map Z P = gaussianReal m v := by
  letI : IsProbabilityMeasure (Measure.map Z P) :=
    Measure.isProbabilityMeasure_map hZ.aemeasurable
  apply measure_eq_of_pos_mgf_on_ray
  · intro θ hθ
    have hA : AEStronglyMeasurable (fun y : ℝ => Real.exp (θ * y))
        (Measure.map Z P) := by fun_prop
    exact (integrable_map_measure hA hZ.aemeasurable).mpr
      (hInt θ hθ)
  · intro θ hθ
    exact integrable_exp_mul_gaussianReal θ
  · intro θ hθ
    have hA : AEStronglyMeasurable (fun y : ℝ => Real.exp (θ * y))
        (Measure.map Z P) := by fun_prop
    have hI := hMGF θ hθ
    simp only [mgf, id] at hI
    rw [integral_map hZ.aemeasurable hA]
    exact hI


/-- Original zero-jump Levy centred normalized increments have exact Gaussian law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Measure.map (fun ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) P =
      gaussianReal 0 (t - s) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have ht : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hs : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
  let Z : Ω → ℝ := fun ω =>
    ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
  have hZ : Measurable Z := by
    dsimp [Z]
    fun_prop
  change Measure.map Z P = gaussianReal 0 (t - s)
  apply gaussianLaw_of_positiveMGF P Z hZ 0 (t - s)
  · intro θ hθ
    simpa [Z] using
      avram_p4_a_gaussian_original_normalised_increment_exponential_integrable
        X X hν rfl hσ s t hst θ hθ.le
  · intro θ hθ
    simpa [Z] using
      avram_p4_a_gaussian_original_normalised_increment_mgf_matches_gaussian
        X X hν rfl hσ s t hst θ hθ.le
