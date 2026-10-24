-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_weighted_primitive_deriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:16:23.140623+00:00
-- url     : https://prove2.me/submissions/28eab4fd-38c3-4659-8a87-4195318a5f7c

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_deriv_eq_continuous_positive
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_primitive_contDiff_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped Topology

theorem solution
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : IntegrableOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ)) volume)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      deriv (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume)) x =
      g x - w * (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * g s ∂volume)) := by
  intro x hx
  let f : ℝ → ℝ := fun s => Real.exp (w * s) * g s
  let G : ℝ → ℝ := fun y => ∫ s in Ioc (0 : ℝ) y, f s ∂volume
  have hGc : ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) := by
    have h := causal_positive_L1_primitive_contDiff_one f hInt hCont
    apply h.congr
    intro y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  have hGdiff : DifferentiableAt ℝ G x :=
    (hGc.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hx)
  have hGder : deriv G x = f x :=
    causal_l1_primitive_deriv_eq_continuous_positive f hInt hCont x hx
  have hInnerDiff : DifferentiableAt ℝ (fun y : ℝ => -w * y) x := by
    fun_prop
  have hExpDiff : DifferentiableAt ℝ
      (fun y : ℝ => Real.exp (-w * y)) x := by
    fun_prop
  have hExpDeriv : deriv (fun y : ℝ => Real.exp (-w * y)) x =
      -w * Real.exp (-w * x) := by
    rw [deriv_exp hInnerDiff, deriv_const_mul_id (-w)]
    ring
  have hProd := deriv_fun_mul hExpDiff hGdiff
  have hCancel : Real.exp (-w * x) * Real.exp (w * x) = 1 := by
    rw [← Real.exp_add]
    have hZero : -w * x + w * x = 0 := by ring
    rw [hZero, Real.exp_zero]
  change deriv (fun y : ℝ => Real.exp (-w * y) * G y) x =
    g x - w * (Real.exp (-w * x) * G x)
  rw [hProd, hExpDeriv, hGder]
  change -w * Real.exp (-w * x) * G x +
      Real.exp (-w * x) * (Real.exp (w * x) * g x) =
      g x - w * (Real.exp (-w * x) * G x)
  rw [← mul_assoc, hCancel, one_mul]
  ring
