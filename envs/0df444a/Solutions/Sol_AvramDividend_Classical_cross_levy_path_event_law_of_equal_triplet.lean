-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_path_event_law_of_equal_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:49:16.201893+00:00
-- url     : https://prove2.me/submissions/0e1d68a7-c94f-439d-a89e-07b6c781f22b

import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Equality of the canonical Lévy triplet transfers every measurable path event across sample spaces. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (E : Set (ℝ≥0 → ℝ)) (hE : MeasurableSet E) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ E} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ E} := by
  apply cross_levy_path_event_law_of_equal_psi X Y ?_ E hE
  intro θ hθ
  change laplaceExponent X.c X.σ X.ν θ =
    laplaceExponent Y.c Y.σ Y.ν θ
  rw [hc, hσ, hν]
