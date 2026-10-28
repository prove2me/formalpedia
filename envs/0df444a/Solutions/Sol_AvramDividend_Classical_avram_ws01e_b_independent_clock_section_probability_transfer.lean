-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_independent_clock_section_probability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:09:51.300782+00:00
-- url     : https://prove2.me/submissions/501598be-6adf-453e-bc9e-d73c397cbf13

import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set

theorem solution
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) [SFinite P]
    (Q : Measure Θ) [SFinite Q]
    (A B : Set (Ω × Θ))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSections : ∀ η : Θ,
      P ((fun ω : Ω => (ω, η)) ⁻¹' A) =
      P ((fun ω : Ω => (ω, η)) ⁻¹' B)) :
    (P.prod Q) A = (P.prod Q) B := by
  rw [Measure.prod_apply_symm hA, Measure.prod_apply_symm hB]
  simp_rw [hSections]
