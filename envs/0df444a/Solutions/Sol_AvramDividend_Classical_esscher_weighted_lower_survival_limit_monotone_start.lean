-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_lower_survival_limit_monotone_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:57:52.026293+00:00
-- url     : https://prove2.me/submissions/7d26c156-ff7b-4bbf-bdd0-e935f7c8e757

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-- The infinite-horizon Esscher survival envelope is monotone in the starting reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x y : ℝ) (hxy : x ≤ y) :
    (⨅ t : ℝ≥0,
      ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤
    (⨅ t : ℝ≥0,
      ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by
  let f : ℝ≥0 → ℝ := fun t =>
    ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P
  let g : ℝ≥0 → ℝ := fun t =>
    ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator
      (fun ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P
  have hBelow : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro z ⟨t, rfl⟩
    exact (esscher_weighted_lower_survival_mass_unit_interval X θ hθ x t).1
  have hPoint : ∀ t : ℝ≥0, f t ≤ g t := by
    intro t
    exact esscher_weighted_lower_survival_mass_monotone_start X θ hθ x y hxy t
  exact ciInf_mono hBelow hPoint
