-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_countable_simple_indicator_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:30:51.485253+00:00
-- url     : https://prove2.me/submissions/bac0b31a-764c-4bc7-8082-b55f13ec0b5f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The integral of a countable nonnegative simple marked integrand is
the exact countable sum of its true cell masses. -/
theorem solution
    {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α)
    (C : ι → Set α) (hC : ∀ i, MeasurableSet (C i))
    (w : ι → ℝ≥0∞) :
    (∫⁻ x, ∑' i, (C i).indicator (fun _ => w i) x ∂μ) =
    ∑' i, w i * μ (C i) := by
  calc
    (∫⁻ x, ∑' i, (C i).indicator (fun _ => w i) x ∂μ) =
        ∑' i, (∫⁻ x, (C i).indicator (fun _ => w i) x ∂μ) := by
          exact lintegral_tsum
            (fun i => (measurable_const.indicator (hC i)).aemeasurable)
    _ = ∑' i, w i * μ (C i) := by
          congr 1
          funext i
          simp [lintegral_indicator (hC i), mul_comm]
