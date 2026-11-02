-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_negative_jump_finite_exponential_measure_interchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:59:24.773012+00:00
-- url     : https://prove2.me/submissions/0d5f610e-d474-42e0-b0f6-3337f664c323

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

/-! Exact signed Bochner finite-sum interchange for an infinite-activity
Lévy measure, assuming integrability only of the vanishing deficits. -/
theorem solution (μ : Measure ℝ) (s : Finset ℕ) (c : ℕ → ℝ)
    (hInt : ∀ k ∈ s, IntegrableOn
      (fun y : ℝ => 1 - Real.exp ((k : ℝ) * y)) (Iio (0 : ℝ)) μ) :
    (∫ y in Iio (0 : ℝ),
      ∑ k ∈ s, c k * (1 - Real.exp ((k : ℝ) * y)) ∂μ) =
      ∑ k ∈ s, c k *
        (∫ y in Iio (0 : ℝ),
          1 - Real.exp ((k : ℝ) * y) ∂μ) := by
  calc
    (∫ y in Iio (0 : ℝ),
      ∑ k ∈ s, c k * (1 - Real.exp ((k : ℝ) * y)) ∂μ) =
        ∑ k ∈ s, (∫ y in Iio (0 : ℝ),
          c k * (1 - Real.exp ((k : ℝ) * y)) ∂μ) := by
            apply integral_finset_sum s
            intro k hk
            exact (hInt k hk).const_mul _
    _ = ∑ k ∈ s, c k *
        (∫ y in Iio (0 : ℝ),
          1 - Real.exp ((k : ℝ) * y) ∂μ) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [integral_const_mul]
