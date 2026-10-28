-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_path_lintegral_eq_of_equal_triplet_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:51:59.152556+00:00
-- url     : https://prove2.me/submissions/30a834c5-3c85-4fde-9388-cfce4898aceb

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Every measurable nonnegative reward of the whole Lévy path has the same
    expectation under processes with the same Lévy triplet. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (g : (ℝ≥0 → ℝ) → ENNReal) (hg : Measurable g) :
    (∫⁻ ω : Ω₁, g (fun t : ℝ≥0 => X.X t ω) ∂P₁) =
    (∫⁻ ω : Ω₂, g (fun t : ℝ≥0 => Y.X t ω) ∂P₂) := by
  let pathX : Ω₁ → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let pathY : Ω₂ → (ℝ≥0 → ℝ) := fun ω t => Y.X t ω
  have hPathX : Measurable pathX :=
    measurable_pi_lambda _ (fun t => X.adapted.measurable (i := t))
  have hPathY : Measurable pathY :=
    measurable_pi_lambda _ (fun t => Y.adapted.measurable (i := t))
  have hLaw : Measure.map pathX P₁ = Measure.map pathY P₂ :=
    cross_levy_whole_path_law_of_equal_triplet X Y hc hσ hν
  change (∫⁻ ω, g (pathX ω) ∂P₁) = (∫⁻ ω, g (pathY ω) ∂P₂)
  rw [← lintegral_map hg hPathX, ← lintegral_map hg hPathY, hLaw]
