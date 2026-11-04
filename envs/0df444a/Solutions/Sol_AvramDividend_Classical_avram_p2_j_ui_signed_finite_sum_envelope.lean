-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_signed_finite_sum_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:51:35.411723+00:00
-- url     : https://prove2.me/submissions/43f9812c-ecbf-4386-8812-6803f464c475

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal BigOperators

/-! Signed real grid sums are dominated by sums of nonnegative mark envelopes. -/
theorem solution
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (b : ι → ENNReal)
    (h : ∀ i ∈ s, ‖a i‖ₑ ≤ b i) :
    ‖∑ i ∈ s, a i‖ₑ ≤ ∑ i ∈ s, b i := by
  classical
  calc
    ‖∑ i ∈ s, a i‖ₑ ≤ ∑ i ∈ s, ‖a i‖ₑ :=
      enorm_sum_le _ _
    _ ≤ ∑ i ∈ s, b i :=
      Finset.sum_le_sum (fun i hi => h i hi)
