-- Prove2me | solution 1 for AvramDividend.Classical.excursion_prokhorov_probability_tight_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:55:24.808707+00:00
-- url     : https://prove2.me/submissions/2880fa4a-3515-49a7-a8d0-2d1283759b29

import Mathlib.MeasureTheory.Measure.Prokhorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set

/-!
Prokhorov compactness makes the closure of a tight probability family
compact. A sequence in that closure therefore has a weakly convergent
strictly increasing subsequence.
-/
theorem solution
    (ν : ℕ → ProbabilityMeasure ℝ)
    (htight : IsTightMeasureSet
      {x : Measure ℝ | ∃ μ ∈ Set.range ν, (μ : Measure ℝ) = x}) :
    ∃ (μ : ProbabilityMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) := by
  have hc : IsCompact (closure (Set.range ν)) :=
    isCompact_closure_of_isTightMeasureSet htight
  have hm : ∀ n : ℕ, ν n ∈ closure (Set.range ν) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  obtain ⟨μ, _, φ, hφ, hlim⟩ := hc.tendsto_subseq hm
  exact ⟨μ, φ, hφ, hlim⟩
