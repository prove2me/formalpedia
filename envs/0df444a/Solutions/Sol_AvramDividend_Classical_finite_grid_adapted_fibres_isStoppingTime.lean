-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_adapted_fibres_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:08:48.008222+00:00
-- url     : https://prove2.me/submissions/29ff945f-e3f1-43e6-a798-7792a438c584

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Adapted measurable fibres on a finite time grid certify a stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hfib : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s}) :
    IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) := by
  classical
  apply isStoppingTime_withTop_of_le_events τ
  intro t
  have hEq : {ω : Ω | τ ω ≤ t} =
      ⋃ s ∈ grid.filter (fun s => s ≤ t),
        {ω : Ω | τ ω = s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨τ ω, ⟨hgrid ω, h⟩, rfl⟩
    · rintro ⟨s, ⟨-, hs⟩, he⟩
      exact he.symm ▸ hs
  rw [hEq]
  apply Finset.measurableSet_biUnion
  intro s hs
  obtain ⟨hsg, hst⟩ := Finset.mem_filter.mp hs
  exact 𝓕.mono hst _ (hfib s hsg)
