-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:38:09.0446+00:00
-- url     : https://prove2.me/submissions/b82c46cd-8709-4383-987f-6cda097a5442

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Finite weighted count sums inherit individually established moment rates. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι)
    (N H : ι → Ω → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (hN : ∀ i ∈ S, Measurable (N i))
    (hH : ∀ i ∈ S, Measurable (H i))
    (hEach : ∀ i ∈ S,
      (∫⁻ ω, H i ω * N i ω ∂μ) = (∫⁻ ω, H i ω ∂μ) * r i) :
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂μ) =
    S.sum (fun i => (∫⁻ ω, H i ω ∂μ) * r i) := by
  calc
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂μ)
        = S.sum (fun i => ∫⁻ ω, H i ω * N i ω ∂μ) := by
            simpa using (lintegral_finset_sum S
              (fun i hi => (hH i hi).mul (hN i hi)))
    _ = S.sum (fun i => (∫⁻ ω, H i ω ∂μ) * r i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hEach i hi
