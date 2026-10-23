-- Prove2me | solution 1 for AvramDividend.Classical.positive_weighted_integral_zero_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:13:56.686087+00:00
-- url     : https://prove2.me/submissions/456ea5d3-859e-4b0c-aa0f-d9d0cb36f694

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (f : ℝ → ℝ) (θ R : ℝ)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hfn : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hInt : IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) * f x)
      (Ioc (0 : ℝ) R) volume)
    (hzero : (∫ x in Ioc (0 : ℝ) R,
      Real.exp (-θ * x) * f x ∂volume) = 0) :
    ∀ x ∈ Ioc (0 : ℝ) R, f x = 0 := by
  let H : ℝ → ℝ := fun x => Real.exp (-θ * x) * f x
  have hnonneg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) R), 0 ≤ H x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hfn x hx.1)
  have hzeroae : H =ᵐ[volume.restrict (Ioc (0 : ℝ) R)]
      (fun _ : ℝ => 0) :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hInt).mp hzero
  have hfcont' : ContinuousOn f (Ioc (0 : ℝ) R) :=
    hfcont.mono (by intro x hx; exact hx.1)
  have hHcont : ContinuousOn H (Ioc (0 : ℝ) R) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn.mul hfcont'
  have heq : Set.EqOn H (fun _ : ℝ => 0) (Ioc (0 : ℝ) R) :=
    MeasureTheory.Measure.eqOn_of_ae_eq hzeroae
      hHcont continuousOn_const
      (Ioc_subset_closure_interior (0 : ℝ) R)
  intro x hx
  have hh : Real.exp (-θ * x) * f x = 0 := heq hx
  exact (mul_eq_zero.mp hh).resolve_left (Real.exp_ne_zero _)
