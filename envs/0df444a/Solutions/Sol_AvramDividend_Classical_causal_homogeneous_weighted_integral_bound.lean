-- Prove2me | solution 1 for AvramDividend.Classical.causal_homogeneous_weighted_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:51:43.214191+00:00
-- url     : https://prove2.me/submissions/9fd9aa80-6c75-4ef9-9f1e-dcb7d71520a7

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K D : ℝ → ℝ) (a β w : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hDc : ContinuousOn D (Ioi (0 : ℝ)))
    (hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |D s| ≤ C)
    (hEq : ∀ x : ℝ, 0 < x →
      a * D x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume) = 0)
    (x : ℝ) (hx : 0 < x) :
    a * (Real.exp (-(w * x)) * |D x|) ≤
      (∫ s in Ioc (0 : ℝ) x,
        (Real.exp (-(w * (x - s))) * |β + K (x - s)|) *
        (Real.exp (-(w * s)) * |D s|) ∂volume) := by
  have hInt := causal_full_kernel_locally_bounded_input_integrable
    K D β hK hDc hDb x hx
  have hEq' : a * D x =
      -(∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume) := by
    have he := hEq x hx
    linarith
  have hNorm :
      |∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume| ≤
      (∫ s in Ioc (0 : ℝ) x,
        |(β + K (x - s)) * D s| ∂volume) := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (f := fun s : ℝ => (β + K (x - s)) * D s)
        (μ := volume.restrict (Ioc (0 : ℝ) x)))
  have hbase : a * |D x| ≤
      (∫ s in Ioc (0 : ℝ) x,
        |(β + K (x - s)) * D s| ∂volume) := by
    calc
      a * |D x| = |a * D x| := by rw [abs_mul, abs_of_pos ha]
      _ = |∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * D s ∂volume| := by rw [hEq', abs_neg]
      _ ≤ _ := hNorm
  calc
    a * (Real.exp (-(w * x)) * |D x|) =
        Real.exp (-(w * x)) * (a * |D x|) := by ring
    _ ≤ Real.exp (-(w * x)) *
          (∫ s in Ioc (0 : ℝ) x,
            |(β + K (x - s)) * D s| ∂volume) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
    _ = ∫ s in Ioc (0 : ℝ) x,
          Real.exp (-(w * x)) * |(β + K (x - s)) * D s| ∂volume := by
      rw [integral_const_mul]
    _ = ∫ s in Ioc (0 : ℝ) x,
          (Real.exp (-(w * (x - s))) * |β + K (x - s)|) *
          (Real.exp (-(w * s)) * |D s|) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with s
      have hexp : -(w * x) = -(w * (x - s)) + -(w * s) := by ring
      rw [abs_mul, hexp, Real.exp_add]
      ring
