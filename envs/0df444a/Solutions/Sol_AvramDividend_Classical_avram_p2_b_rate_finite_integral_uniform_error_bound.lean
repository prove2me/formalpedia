-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_finite_integral_uniform_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:02:22.384954+00:00
-- url     : https://prove2.me/submissions/da7d1157-9fff-4779-9059-2e067b440276

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (δ : ℝ) (hδ : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ δ) :
    |(∫ ω, f ω ∂μ) - (∫ ω, g ω ∂μ)| ≤ δ * μ.real Set.univ := by
  have hnorm : ∀ᵐ ω ∂μ, ‖f ω - g ω‖ ≤ δ := by
    simpa only [Real.norm_eq_abs] using hδ
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun ω => f ω - g ω) hnorm
  rw [integral_sub hf hg] at h
  simpa only [Real.norm_eq_abs] using h
