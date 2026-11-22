-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_clipped_gaussian_active_cell_stopped_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:12:16.66683+00:00
-- url     : https://prove2.me/submissions/bb1bb95b-a9e4-48b8-ab7b-7286c1a38173

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- True clipped-cell activity uses only the stopped history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (σ τ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (s : ℝ≥0) (hτ : ∀ ω, τ ω = min s (σ ω)) :
    ∀ t : ℝ≥0,
      MeasurableSet[𝓕.rightCont t]
        ({ω : Ω | s < σ ω} ∩ {ω : Ω | τ ω ≤ t}):= by
  intro t
  by_cases hst : s ≤ t
  · have hEq : ({ω : Ω | s < σ ω} ∩ {ω : Ω | τ ω ≤ t}) =
        {ω : Ω | s < σ ω} := by
      ext ω
      simp [hτ ω, min_le_iff, hst]
    rw [hEq]
    have hAdapt : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < σ ω} := by
      have hStopSet : MeasurableSet[𝓕.rightCont s] {ω : Ω | σ ω ≤ s} := by
        simpa only [WithTop.coe_le_coe] using hσstop.measurableSet_le s
      have hC : {ω : Ω | s < σ ω} = {ω : Ω | σ ω ≤ s}ᶜ := by
        ext ω
        simp [not_le]
      rw [hC]
      exact hStopSet.compl
    exact (𝓕.rightCont.mono hst {ω : Ω | s < σ ω}) hAdapt
  · have hEmpty : ({ω : Ω | s < σ ω} ∩ {ω : Ω | τ ω ≤ t}) =
        (∅ : Set Ω) := by
      ext ω
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hs
      have hτeq : τ ω = s := by
        rw [hτ ω]
        exact min_eq_left (le_of_lt hs.1)
      exact hst (hτeq ▸ hs.2)
    simpa [hEmpty]
