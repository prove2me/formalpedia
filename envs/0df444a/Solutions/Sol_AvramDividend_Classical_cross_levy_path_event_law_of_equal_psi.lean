-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_path_event_law_of_equal_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:34:49.583336+00:00
-- url     : https://prove2.me/submissions/18f7e96a-dff4-4957-a670-b2926269ae0f

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_marginals
import Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_psi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/--
Equality of positive Lévy Laplace exponents transfers each measurable
whole-path event to an independent realisation on another sample space.
-/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by
  have hPX : Measurable (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) :=
    measurable_pi_lambda _ fun t => X.adapted.measurable
  have hPY : Measurable (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) :=
    measurable_pi_lambda _ fun t => Y.adapted.measurable
  have hLaw := cross_levy_whole_path_law_of_equal_marginals
    X Y (cross_levy_marginal_laws_of_equal_psi X Y hψ)
  calc
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
        (Measure.map (fun ω : Ω₁ => fun t : ℝ≥0 => X.X t ω) P₁) E :=
          (Measure.map_apply hPX hE).symm
    _ = (Measure.map (fun ω : Ω₂ => fun t : ℝ≥0 => Y.X t ω) P₂) E :=
      congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ E) hLaw
    _ = P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} :=
      Measure.map_apply hPY hE
