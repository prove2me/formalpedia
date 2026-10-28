-- Prove2me | solution 1 for AvramDividend.Classical.chat08_stopping_time_early_observed_switch
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:24:31.901924+00:00
-- url     : https://prove2.me/submissions/c88a87e4-0566-4d87-b3ce-b64d0aefa857

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (hlater : ∀ ω, (s : WithTop ℝ≥0) ≤ τ ω) :
    IsStoppingTime ℱ
      (fun ω => if ω ∈ A then (s : WithTop ℝ≥0) else τ ω) := by
  intro i
  have cs : ((s : WithTop ℝ≥0) ≤ i) ↔ s ≤ i := WithTop.coe_le_coe
  by_cases hsi : s ≤ i
  · have : {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else τ ω) ≤ i} = A ∪ (Aᶜ ∩ {ω | τ ω ≤ i}) := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      split_ifs with h
      · exact ⟨fun _ => Or.inl h, fun _ => cs.2 hsi⟩
      · exact ⟨fun h' => Or.inr ⟨h, h'⟩, fun h' => h'.elim (fun h'' => absurd h'' h) (fun h'' => h''.2)⟩
    rw [this]
    exact (ℱ.mono hsi _ hA).union ((ℱ.mono hsi _ hA).compl.inter (hτ i))
  · have : {ω | (if ω ∈ A then (s : WithTop ℝ≥0) else τ ω) ≤ i} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      split_ifs
      · exact fun h' => hsi (cs.1 h')
      · exact fun h => hsi (cs.1 ((hlater ω).trans h))
    rw [this]; exact @MeasurableSet.empty Ω (ℱ i)
