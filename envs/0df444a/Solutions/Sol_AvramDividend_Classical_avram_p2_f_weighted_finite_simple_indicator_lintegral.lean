-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_finite_simple_indicator_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:37:37.000246+00:00
-- url     : https://prove2.me/submissions/0d9bd210-6f0b-4cb2-8642-e586e74a1d74

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A finite nonnegative simple marked integrand integrates to the
sum of its original measurable cell masses, with no disjointness needed. -/
theorem solution
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι)
    (C : ι → Set α) (hC : ∀ i ∈ S, MeasurableSet (C i))
    (w : ι → ℝ≥0∞) :
    (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => w i) x) ∂μ) =
    S.sum (fun i => w i * μ (C i)) := by
  calc
    (∫⁻ x, S.sum (fun i => (C i).indicator (fun _ => w i) x) ∂μ) =
        S.sum (fun i => (∫⁻ x, (C i).indicator (fun _ => w i) x ∂μ)) := by
          exact lintegral_finset_sum S
            (by
              intro i hi
              exact measurable_const.indicator (hC i hi))
    _ = S.sum (fun i => w i * μ (C i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [lintegral_indicator (hC i hi), mul_comm]
