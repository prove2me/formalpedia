-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb74_finite_double_integral_uniform_kernel_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:04:00.400207+00:00
-- url     : https://prove2.me/submissions/46891df6-512d-428b-a43c-485c336a2c1f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℕ → α → β → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hBound : ∀ n a b, |H n a b| ≤ K) :
    ∀ n : ℕ,
      ‖∫ a, ∫ b, H n a b ∂ν ∂μ‖ ≤
        (K * ν.real Set.univ) * μ.real Set.univ := by
  intro n
  have hInner : ∀ a : α,
      ‖∫ b, H n a b ∂ν‖ ≤ K * ν.real Set.univ := by
    intro a
    apply norm_integral_le_of_norm_le_const
    filter_upwards [] with b
    simpa only [Real.norm_eq_abs] using hBound n a b
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with a
  exact hInner a
