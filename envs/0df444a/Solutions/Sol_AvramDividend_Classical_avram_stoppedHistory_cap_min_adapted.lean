-- Prove2me | solution 1 for AvramDividend.Classical.avram_stoppedHistory_cap_min_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:42:59.049308+00:00
-- url     : https://prove2.me/submissions/539c8f8a-c205-440b-a3c7-6d4c51468a38

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (H : ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        ((A ∩ {ω : Ω | τ ω ≤ H}) ∩
          {ω : Ω | min (τ ω) H ≤ s}) := by
  intro s
  by_cases hs : H ≤ s
  · have he : {ω : Ω | min (τ ω) H ≤ s} = univ := by
      ext ω
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact (min_le_right _ _).trans hs
    simpa only [he, inter_univ] using
      (𝓕.mono hs _ (hA H))
  · have hlt : s < H := lt_of_not_ge hs
    have hset : {ω : Ω | min (τ ω) H ≤ s} =
        {ω : Ω | τ ω ≤ s} := by
      ext ω
      simp only [mem_setOf_eq, min_le_iff]
      constructor
      · intro hh
        exact hh.resolve_right (not_le.mpr hlt)
      · exact Or.inl
    have he :
        (A ∩ {ω : Ω | τ ω ≤ H}) ∩
          {ω : Ω | min (τ ω) H ≤ s} =
        A ∩ {ω : Ω | τ ω ≤ s} := by
      rw [hset]
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq]
      constructor
      · intro hh
        exact ⟨hh.1.1, hh.2⟩
      · intro hh
        exact ⟨⟨hh.1, hh.2.trans hlt.le⟩, hh.2⟩
    rw [he]
    exact hA s
