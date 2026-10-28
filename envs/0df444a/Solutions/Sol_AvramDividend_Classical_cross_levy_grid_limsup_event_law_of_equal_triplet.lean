-- Prove2me | solution 1 for AvramDividend.Classical.cross_levy_grid_limsup_event_law_of_equal_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:13:47.844255+00:00
-- url     : https://prove2.me/submissions/0a717e32-08ac-4f43-9b27-798f6fcc43c7

import Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_event_measurable
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_triplet
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The canonical triplet uniquely determines the probability of every
infinitely recurrent downward-grid-increment event. -/
theorem solution
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0)) (a : ℝ) :
    P₁ {ω : Ω₁ | (fun t : ℝ≥0 => X.X t ω) ∈ (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
      ⋃ ij ∈ grid n.1,
        {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a})} =
    P₂ {ω : Ω₂ | (fun t : ℝ≥0 => Y.X t ω) ∈ (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
      ⋃ ij ∈ grid n.1,
        {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a})} := by
  exact cross_levy_path_event_law_of_equal_triplet
    X Y hc hσ hν _ (downward_grid_limsup_event_measurable grid a)
