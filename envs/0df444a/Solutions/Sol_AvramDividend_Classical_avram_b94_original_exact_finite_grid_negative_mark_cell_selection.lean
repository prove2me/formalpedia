-- Prove2me | solution 1 for AvramDividend.Classical.avram_b94_original_exact_finite_grid_negative_mark_cell_selection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:15:53.085142+00:00
-- url     : https://prove2.me/submissions/92f08b40-8758-4d8f-ab2c-ad06184bb0ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The marked finite cells are exactly those containing a source jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) :
    ∃ J : Ω → Finset ℕ,
      (∀ ω i, i ∈ J ω ↔ i ∈ S ∧
        ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      (∀ ω i, i ∈ S → i ∉ J ω →
        ∀ u : ℝ≥0, s i ω < u → u ≤ t i ω →
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) := by
  classical
  let J : Ω → Finset ℕ := fun ω =>
    S.filter (fun i => ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
  have hChar (ω : Ω) (i : ℕ) :
      i ∈ J ω ↔ i ∈ S ∧
        ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    simp only [J, Finset.mem_filter]
  refine ⟨J, hChar, ?_⟩
  intro ω i hi hnot u hsu hut
  by_contra hne
  exact hnot ((hChar ω i).2 ⟨hi, ⟨u, hsu, hut, hne⟩⟩)
