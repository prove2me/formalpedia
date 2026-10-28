-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_lower_survival_limit_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:58:33.176192+00:00
-- url     : https://prove2.me/submissions/c02b2fbf-c478-4ea8-8166-3dbc7c376414

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-- The infimum over finite Esscher-survival horizons remains a subprobability mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    0 ≤
      (⨅ t : ℝ≥0,
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
    ∧
      (⨅ t : ℝ≥0,
        ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤ 1 := by
  let f : ℝ≥0 → ℝ := fun t =>
    ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P
  have hBounds : ∀ t : ℝ≥0, 0 ≤ f t ∧ f t ≤ 1 := by
    intro t
    exact esscher_weighted_lower_survival_mass_unit_interval X θ hθ x t
  have hBelow : BddBelow (Set.range f) := by
    refine ⟨0, ?_⟩
    rintro z ⟨t, rfl⟩
    exact (hBounds t).1
  constructor
  · exact le_ciInf (fun t => (hBounds t).1)
  · exact (ciInf_le hBelow (0 : ℝ≥0)).trans (hBounds 0).2
