-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_weighted_primitive_deriv_eq_local
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:17:01.00937+00:00
-- url     : https://prove2.me/submissions/f32721f4-ae86-46f0-9774-228644ebdf00

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_deriv_eq_continuous_positive
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

/-- Termwise differentiation of an exponentially weighted causal primitive
under local positive-time integrability. -/
theorem solution
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
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
  have hAt : ContinuousAt f x := hCont.continuousAt (Ioi_mem_nhds hx)
  have hMeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hCont) x hx
  have hFTC : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, f s)
      (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hInt x hx) hMeas hAt
  have hDeriv : HasDerivAt G (f x) x := by
    apply hFTC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  have hGdiff : DifferentiableAt ℝ G x := hDeriv.differentiableAt
  have hGder : deriv G x = f x := hDeriv.deriv
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
