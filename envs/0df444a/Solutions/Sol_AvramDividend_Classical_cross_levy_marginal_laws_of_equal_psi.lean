-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_marginal_laws_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:52:17.893437+00:00
-- url     : https://prove2.me/submissions/c648e472-e8b1-46a5-ab7a-aeb40899e40d

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
Equal Laplace exponents determine each time marginal of distinct
spectrally negative Lévy realisations via positive-MGF uniqueness.
-/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ) :
    ∀ t : ℝ≥0,
      Measure.map (X.X t) P₁ = Measure.map (Y.X t) P₂ := by
  letI : IsProbabilityMeasure P₁ := X.isProbability
  letI : IsProbabilityMeasure P₂ := Y.isProbability
  intro t
  have hX : Measurable (X.X t) := X.adapted.measurable
  have hY : Measurable (Y.X t) := Y.adapted.measurable
  letI : IsProbabilityMeasure (Measure.map (X.X t) P₁) := by
    refine ⟨?_⟩
    rw [Measure.map_apply hX MeasurableSet.univ]
    simpa only [Set.preimage_univ] using (measure_univ : P₁ Set.univ = 1)
  letI : IsProbabilityMeasure (Measure.map (Y.X t) P₂) := by
    refine ⟨?_⟩
    rw [Measure.map_apply hY MeasurableSet.univ]
    simpa only [Set.preimage_univ] using (measure_univ : P₂ Set.univ = 1)
  have he (θ : ℝ) : Measurable (fun x : ℝ => Real.exp (θ * x)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
  apply measure_eq_of_pos_mgf_on_ray
  · intro θ hθ
    apply (integrable_map_measure (he θ).aestronglyMeasurable hX.aemeasurable).2
    simpa only [Function.comp_def] using (X.laplace t θ (le_of_lt hθ)).1
  · intro θ hθ
    apply (integrable_map_measure (he θ).aestronglyMeasurable hY.aemeasurable).2
    simpa only [Function.comp_def] using (Y.laplace t θ (le_of_lt hθ)).1
  · intro θ hθ
    calc
      (∫ x : ℝ, Real.exp (θ * x) ∂Measure.map (X.X t) P₁) =
          ∫ ω, Real.exp (θ * X.X t ω) ∂P₁ := by
            exact integral_map hX.aemeasurable (he θ).aestronglyMeasurable
      _ = Real.exp ((t : ℝ) * X.ψ θ) := (X.laplace t θ (le_of_lt hθ)).2
      _ = Real.exp ((t : ℝ) * Y.ψ θ) := by rw [hψ θ hθ]
      _ = (∫ ω, Real.exp (θ * Y.X t ω) ∂P₂) :=
        (Y.laplace t θ (le_of_lt hθ)).2.symm
      _ = (∫ x : ℝ, Real.exp (θ * x) ∂Measure.map (Y.X t) P₂) := by
        exact (integral_map hY.aemeasurable (he θ).aestronglyMeasurable).symm
