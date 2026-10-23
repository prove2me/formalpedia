-- Prove2me | solution 2 for AvramDividend.Classical.causal_homogeneous_weighted_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:52:58.78946+00:00
-- url     : https://prove2.me/submissions/1c2c56dd-e513-499f-80b9-545f1b3cbec5

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_locally_bounded_input_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

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
  have hInt : IntegrableOn (fun s : ℝ =>
      (β + K (x - s)) * D s) (Ioc (0 : ℝ) x) volume :=
    causal_full_kernel_locally_bounded_input_integrable
      K D β hK hDc hDb x hx
  have hvalue : a * D x =
      -(∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * D s ∂volume) := by
    linarith [hEq x hx]
  have habs : a * |D x| =
      |∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * D s ∂volume| := by
    have hh := congrArg abs hvalue
    simpa only [abs_mul, abs_of_nonneg ha.le, abs_neg] using hh
  have hnorm :
      |∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * D s ∂volume| ≤
      ∫ s in Ioc (0 : ℝ) x,
          |(β + K (x - s)) * D s| ∂volume := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := volume.restrict (Ioc (0 : ℝ) x))
        (fun s : ℝ => (β + K (x - s)) * D s))
  have hpoint (s : ℝ) :
      Real.exp (-(w * x)) * |(β + K (x - s)) * D s| =
        (Real.exp (-(w * (x - s))) * |β + K (x - s)|) *
          (Real.exp (-(w * s)) * |D s|) := by
    have hexp : Real.exp (-(w * x)) =
        Real.exp (-(w * (x - s))) * Real.exp (-(w * s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [abs_mul, hexp]
    ring
  calc
    a * (Real.exp (-(w * x)) * |D x|)
        = Real.exp (-(w * x)) * (a * |D x|) := by ring
    _ = Real.exp (-(w * x)) *
        |∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * D s ∂volume| := by rw [habs]
    _ ≤ Real.exp (-(w * x)) *
        (∫ s in Ioc (0 : ℝ) x,
          |(β + K (x - s)) * D s| ∂volume) :=
            mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
    _ = ∫ s in Ioc (0 : ℝ) x,
        Real.exp (-(w * x)) * |(β + K (x - s)) * D s| ∂volume := by
          rw [integral_const_mul]
    _ = ∫ s in Ioc (0 : ℝ) x,
        (Real.exp (-(w * (x - s))) * |β + K (x - s)|) *
          (Real.exp (-(w * s)) * |D s|) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with s
          exact hpoint s
