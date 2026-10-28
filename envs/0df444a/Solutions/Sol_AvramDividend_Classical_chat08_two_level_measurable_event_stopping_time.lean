-- Prove2me | solution 1 for AvramDividend.Classical.chat08_two_level_measurable_event_stopping_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:24:24.149507+00:00
-- url     : https://prove2.me/submissions/c510aa3a-c139-4def-b50d-c608eb1cc7d4

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    IsStoppingTime ℱ
      (fun ω => if ω ∈ A then (s : WithTop ℝ≥0) else (t : WithTop ℝ≥0)) := by
  intro i
  have cs : ((s : WithTop ℝ≥0) ≤ i) ↔ s ≤ i := WithTop.coe_le_coe
  have ct : ((t : WithTop ℝ≥0) ≤ i) ↔ t ≤ i := WithTop.coe_le_coe
  by_cases hti : t ≤ i
  · have : {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else (t : WithTop ℝ≥0)) ≤ i} = Set.univ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      split_ifs
      · exact cs.2 (hst.trans hti)
      · exact ct.2 hti
    rw [this]; exact @MeasurableSet.univ Ω (ℱ i)
  · by_cases hsi : s ≤ i
    · have : {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else (t : WithTop ℝ≥0)) ≤ i} = A := by
        ext ω; simp only [Set.mem_ofPred_eq]
        split_ifs with h
        · exact ⟨fun _ => h, fun _ => cs.2 hsi⟩
        · exact ⟨fun h' => absurd (ct.1 h') hti, fun h' => absurd h' h⟩
      rw [this]; exact ℱ.mono hsi _ hA
    · have : {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else (t : WithTop ℝ≥0)) ≤ i} = ∅ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        split_ifs
        · exact fun h' => hsi (cs.1 h')
        · exact fun h' => hti (ct.1 h')
      rw [this]; exact @MeasurableSet.empty Ω (ℱ i)
