-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_positive_event_integrable_geometric_section
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:09.200897+00:00
-- url     : https://prove2.me/submissions/31bf4d84-245c-4fc0-9b78-1fa5a7ee75a7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- A nonnull path event contains an integrable section of any integrable product function. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : unitInterval) (A : Set Ω) (hA : P A ≠ 0)
    (f : Ω × Nat → Real)
    (hf : Integrable f (P.prod (geometricMeasure p))) :
    ∃ ω ∈ A, Integrable (fun k : Nat => f (ω, k)) (geometricMeasure p) := by
  have hsections : ∀ᵐ ω ∂P,
      Integrable (fun k : Nat => f (ω, k)) (geometricMeasure p) :=
    Integrable.prod_right_ae hf
  exact P.exists_mem_of_measure_ne_zero_of_ae hA
    (ae_restrict_of_ae hsections)
