-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_negative_restricted_rate_weighted_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:04:20.442686+00:00
-- url     : https://prove2.me/submissions/70bb93c1-489b-49f5-a968-3c61177b26da

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-! Matching negative-band Borel rates determine every weighted mark integral. -/
theorem solution
    (μ ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hEq : ∀ C : Set ℝ, MeasurableSet C → C ⊆ B → μ C = ν C)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in B, g y ∂μ) = (∫⁻ y in B, g y ∂ν) := by
  have hres : μ.restrict B = ν.restrict B := by
    ext C hC
    rw [Measure.restrict_apply hC, Measure.restrict_apply hC]
    exact hEq (C ∩ B) (hC.inter hB) (inter_subset_right)
  change (∫⁻ y, g y ∂μ.restrict B) =
    (∫⁻ y, g y ∂ν.restrict B)
  rw [hres]
