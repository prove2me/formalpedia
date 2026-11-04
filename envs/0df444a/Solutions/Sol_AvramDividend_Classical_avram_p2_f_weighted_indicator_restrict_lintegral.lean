-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_indicator_restrict_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:38:14.451516+00:00
-- url     : https://prove2.me/submissions/d8a79c51-48c0-4233-ab5b-79809be55873

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Move an actual measurable past-event restriction through a weighted count. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (H N : Ω → ℝ≥0∞) :
    (∫⁻ ω, H ω * A.indicator N ω ∂μ) =
    (∫⁻ ω in A, H ω * N ω ∂μ) := by
  have hpoint :
      (fun ω => H ω * A.indicator N ω) =
      A.indicator (fun ω => H ω * N ω) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  rw [hpoint, lintegral_indicator hA]
