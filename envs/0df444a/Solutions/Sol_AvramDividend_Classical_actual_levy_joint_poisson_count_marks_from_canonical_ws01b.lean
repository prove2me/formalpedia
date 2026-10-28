-- Prove2me | solution 1 for AvramDividend.Classical.actual_levy_joint_poisson_count_marks_from_canonical_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:27:05.770995+00:00
-- url     : https://prove2.me/submissions/3e9e470e-e9bc-404c-a348-a279dc2d275d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The complete *joint* count/mark Poisson law of a canonical path
functional transfers to any Lévy process having the same triplet. -/
theorem solution
    {Ω₁ Ω₂ E : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    [MeasurableSpace E]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (Fpath : (ℝ≥0 → ℝ) → ℕ × (ℕ → E))
    (hF : Measurable Fpath)
    (r : ℝ≥0) (η : Measure (ℕ → E))
    (hYlaw : HasLaw
      (fun ω : Ω₂ => Fpath (fun t : ℝ≥0 => Y.X t ω))
      ((poissonMeasure r).prod η) P₂) :
    HasLaw
      (fun ω : Ω₁ => Fpath (fun t : ℝ≥0 => X.X t ω))
      ((poissonMeasure r).prod η) P₁ := by
  let pathX : Ω₁ → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  let pathY : Ω₂ → (ℝ≥0 → ℝ) := fun ω t => Y.X t ω
  have hPathX : Measurable pathX := by
    exact measurable_pi_lambda _ (fun t => X.adapted.measurable (i := t))
  have hPathY : Measurable pathY := by
    exact measurable_pi_lambda _ (fun t => Y.adapted.measurable (i := t))
  have hlaw : Measure.map pathX P₁ = Measure.map pathY P₂ :=
    cross_levy_whole_path_law_of_equal_triplet X Y hc hσ hν
  have hm := congrArg (Measure.map Fpath) hlaw
  have hxmap :
      Measure.map Fpath (Measure.map pathX P₁) =
        Measure.map (Fpath ∘ pathX) P₁ :=
    Measure.map_map hF hPathX
  have hymap :
      Measure.map Fpath (Measure.map pathY P₂) =
        Measure.map (Fpath ∘ pathY) P₂ :=
    Measure.map_map hF hPathY
  refine ⟨(hF.comp hPathX).aemeasurable, ?_⟩
  change Measure.map (Fpath ∘ pathX) P₁ = (poissonMeasure r).prod η
  rw [hxmap, hymap] at hm
  exact hm.trans hYlaw.map_eq
