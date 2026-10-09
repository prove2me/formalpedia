-- Prove2me | solution 1 for AvramDividend.Classical.integrable_prod_of_slice_norm_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:22:07.804989+00:00
-- url     : https://prove2.me/submissions/fd202ee0-4c44-4e3c-8dd5-c9e6a52eb11a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (f : ℝ × ℝ → ℝ) (C : ℝ)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hsections : ∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ)
    (hnorm_meas : AEStronglyMeasurable
      (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν)
    (hmin : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (hdom : ∀ᵐ y ∂ν,
      (∫ x, ‖f (x, y)‖ ∂μ) ≤ C * min 1 (y ^ 2)) :
    Integrable f (μ.prod ν) := by
  have hmajor :
      Integrable (fun y : ℝ => C * min 1 (y ^ 2)) ν :=
    hmin.const_mul C
  have hinner :
      Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν := by
    apply hmajor.mono' hnorm_meas
    filter_upwards [hdom] with y hy
    have hnonneg : 0 ≤ ∫ x, ‖f (x, y)‖ ∂μ :=
      integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hy
  exact (integrable_prod_iff' hf).mpr ⟨hsections, hinner⟩
