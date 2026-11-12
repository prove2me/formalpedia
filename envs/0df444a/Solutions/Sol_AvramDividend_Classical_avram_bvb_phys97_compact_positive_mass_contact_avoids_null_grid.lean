-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys97_compact_positive_mass_contact_avoids_null_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:31:46.953884+00:00
-- url     : https://prove2.me/submissions/059b3e97-3002-4892-807f-04cd4690fdf8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A null family of grid points can be avoided by a compact set carrying
positive measure.  Compactness alone does not imply zero contact occupation. -/
theorem solution
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    (μ : Measure α) [μ.InnerRegularCompactLTTop]
    (A N : Set α) (hA : MeasurableSet A) (hN : MeasurableSet N)
    (hNzero : μ N = 0) (hAf : μ A ≠ ⊤) (hApos : 0 < μ A) :
    ∃ K : Set α, IsCompact K ∧ K ⊆ A ∧ Disjoint K N ∧ 0 < μ K := by
  have hμ : μ (A \ N) = μ A := measure_sdiff_null hNzero
  have hAf' : μ (A \ N) ≠ ⊤ := by simpa [hμ] using hAf
  have hApos' : 0 < μ (A \ N) := by simpa [hμ] using hApos
  obtain ⟨K, hKsub, hKcompact, hKpos⟩ :=
    (hA.diff hN).exists_lt_isCompact_of_ne_top hAf' hApos'
  refine ⟨K, hKcompact, hKsub.trans diff_subset, ?_, hKpos⟩
  apply disjoint_left.mpr
  intro x hxK hxN
  exact (hKsub hxK).2 hxN
