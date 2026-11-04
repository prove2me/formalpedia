-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_count_restrict_map_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:35:57.807036+00:00
-- url     : https://prove2.me/submissions/7c56ead3-0e93-47d9-8e22-a13a18dd4a7b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Literal mapped intrinsic counts agree with restricted rectangle preimages. -/
theorem solution
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (jump : α → β × γ) (hjump : Measurable jump)
    (J : Set α) (time : Set β) (marks : Set γ)
    (htime : MeasurableSet time) (hmarks : MeasurableSet marks) :
    ((Measure.count.restrict J).map jump) (time ×ˢ marks) =
      Measure.count {u : α | u ∈ J ∧ jump u ∈ time ×ˢ marks} := by
  rw [Measure.map_apply hjump (htime.prod hmarks)]
  rw [Measure.restrict_apply (hjump (htime.prod hmarks))]
  congr 1
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, and_comm]
