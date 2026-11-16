-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:18:06.459748+00:00
-- url     : https://prove2.me/submissions/8a810d90-9f06-4272-81fb-633023b6bcbd

import Mathlib.MeasureTheory.Measure.MeasureSpace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (R : Ω → Prop)
    (hPos : 0 < P E)
    (hAe : ∀ᵐ ω ∂P, ω ∈ E → R ω) :
    0 < P {ω | ω ∈ E ∧ R ω} := by
  have hm : P ({ω | ω ∈ E → R ω} ∩ E) = P E :=
    Measure.measure_inter_eq_of_ae hAe
  have hs : {ω | ω ∈ E → R ω} ∩ E =
      {ω | ω ∈ E ∧ R ω} := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      exact ⟨h.2, h.1 h.2⟩
    · intro h
      exact ⟨fun _ => h.2, h.1⟩
  rw [hs] at hm
  rw [hm]
  exact hPos
