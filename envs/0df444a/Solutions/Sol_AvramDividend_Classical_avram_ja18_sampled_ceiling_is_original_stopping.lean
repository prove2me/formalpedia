-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_sampled_ceiling_is_original_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:44:18.78752+00:00
-- url     : https://prove2.me/submissions/d4d8ac6d-8488-43ce-bfb4-3a7b3510a3fe

import Mathlib.Probability.Process.Stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Level-event measurability of a sampled index yields true
continuous-time stopping measurability of its physical grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (K : Ω → ℕ)
    (hEvents : ∀ i, MeasurableSet[𝓕.rightCont (e i)]
      {ω : Ω | K ω ≤ i}) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (e (K ω) : WithTop ℝ≥0)) := by
  intro t
  have hSet : {ω : Ω | (e (K ω) : WithTop ℝ≥0) ≤ t} =
      ⋃ i : ℕ, {ω : Ω | K ω ≤ i ∧ e i ≤ t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, WithTop.coe_le_coe]
    constructor
    · intro h
      exact ⟨K ω, le_rfl, h⟩
    · rintro ⟨i, hi, ht⟩
      exact (he hi).trans ht
  rw [hSet]
  apply MeasurableSet.iUnion
  intro i
  by_cases ht : e i ≤ t
  · have hMeas : MeasurableSet[𝓕.rightCont t] {ω : Ω | K ω ≤ i} :=
      (𝓕.rightCont.mono ht) _ (hEvents i)
    simpa [ht] using hMeas
  · simp [ht]
