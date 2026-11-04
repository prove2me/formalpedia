-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_countable_predictable_cell_lintegral_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:11:37.925663+00:00
-- url     : https://prove2.me/submissions/7300632e-9648-44de-ad3d-009b14d733ae

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Countable nonnegative predictable marked-cell compensation from genuine
individual weighted means, including infinitely many active jumps. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω)
    (N H : ι → Ω → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (hN : ∀ i, Measurable (N i))
    (hH : ∀ i, Measurable (H i))
    (hEach : ∀ i,
      (∫⁻ ω, H i ω * N i ω ∂μ) = (∫⁻ ω, H i ω ∂μ) * r i) :
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂μ) =
    ∑' i, (∫⁻ ω, H i ω ∂μ) * r i := by
  calc
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂μ)
        = ∑' i, (∫⁻ ω, H i ω * N i ω ∂μ) := by
            exact lintegral_tsum
              (fun i => ((hH i).mul (hN i)).aemeasurable)
    _ = ∑' i, (∫⁻ ω, H i ω ∂μ) * r i := by
          congr 1
          funext i
          exact hEach i
