-- Prove2me | solution 1 for AvramDividend.Classical.avram_b160_original_true_finite_grid_marked_cells_and_all_unmarked_intervals_jumpfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:27.931231+00:00
-- url     : https://prove2.me/submissions/b151d704-38d1-4c10-a639-9578ed50275f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original source jump-containing cells of an arbitrary finite stopped grid form a Finset; unmarked cells are physically jumpfree throughout their own half-open intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) :
    ∃ J : Ω → Finset ℕ,
      (∀ ω i, i ∈ J ω ↔ i ∈ S ∧
        ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      (∀ ω, J ω ⊆ S) ∧
      (∀ ω i, i ∈ S → i ∉ J ω → ∀ u : ℝ≥0,
        s i ω < u → u ≤ t i ω →
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) := by
  classical
  let J : Ω → Finset ℕ := fun ω =>
    S.filter (fun i => ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
  refine ⟨J, ?_, ?_, ?_⟩
  · intro ω i
    exact Finset.mem_filter
  · intro ω i hi
    exact (Finset.mem_filter.mp hi).1
  · intro ω i hi hj u hsu hut
    by_contra hne
    exact hj (Finset.mem_filter.mpr ⟨hi, ⟨u, hsu, hut, hne⟩⟩)
