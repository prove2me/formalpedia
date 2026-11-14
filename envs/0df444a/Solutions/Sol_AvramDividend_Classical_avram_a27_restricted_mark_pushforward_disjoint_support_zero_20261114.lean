-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_restricted_mark_pushforward_disjoint_support_zero_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:47:42.987217+00:00
-- url     : https://prove2.me/submissions/4fca1110-b9ea-45c2-b87a-886a08e2fd66

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- A restricted source point measure assigns zero mass after a measurable pushforward to an avoided marked set. -/
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (S : Set α) (f : α → β)
    (hf : Measurable f) (E : Set β) (hE : MeasurableSet E)
    (hNo : ∀ x ∈ S, f x ∉ E) :
    (μ.restrict S).map f E = 0 := by
  have hEmpty : S ∩ f ⁻¹' E = ∅ := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact (hNo x hx hfx).elim
    · simp
  calc
    (μ.restrict S).map f E = (μ.restrict S) (f ⁻¹' E) :=
      Measure.map_apply hf hE
    _ = μ (S ∩ f ⁻¹' E) := by
      rw [Measure.restrict_apply (hf hE)]
      rw [Set.inter_comm]
    _ = 0 := by rw [hEmpty]; exact measure_empty
