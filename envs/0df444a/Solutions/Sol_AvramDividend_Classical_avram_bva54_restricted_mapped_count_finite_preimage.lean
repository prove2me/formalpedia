-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva54_restricted_mapped_count_finite_preimage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:38:37.901762+00:00
-- url     : https://prove2.me/submissions/5671791a-db4b-452a-8106-2fb16bb95327

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Finite mapped counting mass makes the selected original source-time set finite. -/
theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α]
    (A : Set α) (f : α → β) (hf : Measurable f)
    (B : Set β) (hB : MeasurableSet B)
    (hFinite : ((Measure.count.restrict A).map f) B < ⊤) :
    (A ∩ f ⁻¹' B).Finite := by
  have hpre : MeasurableSet (f ⁻¹' B) := hB.preimage hf
  rw [Measure.map_apply hf hB, Measure.restrict_apply hpre] at hFinite
  have hSource : ((f ⁻¹' B) ∩ A).Finite :=
    (Measure.count_apply_lt_top).mp hFinite
  simpa [Set.inter_comm] using hSource
