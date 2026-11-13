-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_predictable_section_measurable_public
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T14:48:33.973066+00:00
-- url     : https://prove2.me/submissions/18f5e21f-3077-4957-894a-8580034846bd

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- The section `t ↦ (t, ω)` is measurable for the predictable σ-algebra, since its preimages of
the generating rectangles `{0} × A` and `(i, ∞) × A` are respectively `{0}` (or `∅`) and
`(i, ∞)` (or `∅`). -/
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable ℝ≥0 (ℝ≥0 × Ω) inferInstance 𝓕.predictable (fun t => (t, ω)) := by
  unfold Filtration.predictable
  apply measurable_generateFrom
  intro t ht
  rcases ht with ⟨A, -, rfl⟩ | ⟨i, A, -, rfl⟩
  · by_cases hω : ω ∈ A
    · have hpre : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ({⊥} ×ˢ A) = {⊥} := by
        ext t
        simp [Set.mem_prod, hω]
      rw [hpre]
      exact measurableSet_singleton ⊥
    · have hpre : (fun t : ℝ≥0 => (t, ω)) ⁻¹' ({⊥} ×ˢ A) = ∅ := by
        ext t
        simp [Set.mem_prod, hω]
      rw [hpre]
      exact MeasurableSet.empty
  · by_cases hω : ω ∈ A
    · have hpre : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (Set.Ioi i ×ˢ A) = Set.Ioi i := by
        ext t
        simp [Set.mem_preimage, Set.mem_prod, hω]
      rw [hpre]
      exact measurableSet_Ioi
    · have hpre : (fun t : ℝ≥0 => (t, ω)) ⁻¹' (Set.Ioi i ×ˢ A) = ∅ := by
        ext t
        simp [Set.mem_preimage, Set.mem_prod, hω]
      rw [hpre]
      exact MeasurableSet.empty
