-- Prove2me | solution 1 for AvramDividend.Classical.actual_levy_poisson_count_law_from_canonical_path_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:13:48.766834+00:00
-- url     : https://prove2.me/submissions/83c4f93b-803e-4ae7-a49c-af7dc2e3e194

import Mathlib
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- A genuine Poisson count law for a measurable jump-count functional
of a canonical Lévy path transfers to any actual Lévy process having
the same triplet, without only testing the zero-count event. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (count : (ℝ≥0 → ℝ) → ℕ) (hcount : Measurable count)
    (r : ℝ≥0)
    (hYlaw : HasLaw
      (fun ω : Ω₂ => count (fun t : ℝ≥0 => Y.X t ω))
      (poissonMeasure r) P₂) :
    HasLaw
      (fun ω : Ω₁ => count (fun t : ℝ≥0 => X.X t ω))
      (poissonMeasure r) P₁ := by
  let pathX : Ω₁ → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let pathY : Ω₂ → (ℝ≥0 → ℝ) := fun ω t => Y.X t ω
  have hPathX : Measurable pathX := by
    exact measurable_pi_lambda _ (fun t => X.adapted.measurable (i := t))
  have hPathY : Measurable pathY := by
    exact measurable_pi_lambda _ (fun t => Y.adapted.measurable (i := t))
  have hpathLaw : Measure.map pathX P₁ = Measure.map pathY P₂ :=
    cross_levy_whole_path_law_of_equal_triplet X Y hc hσ hν
  have hcountLaw := congrArg (Measure.map count) hpathLaw
  refine ⟨(hcount.comp hPathX).aemeasurable, ?_⟩
  have hmapX :
      Measure.map count (Measure.map pathX P₁) =
        Measure.map (count ∘ pathX) P₁ :=
    Measure.map_map hcount hPathX
  have hmapY :
      Measure.map count (Measure.map pathY P₂) =
        Measure.map (count ∘ pathY) P₂ :=
    Measure.map_map hcount hPathY
  change Measure.map (count ∘ pathX) P₁ = poissonMeasure r
  rw [hmapX, hmapY] at hcountLaw
  exact hcountLaw.trans hYlaw.map_eq
