-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_weighted_primitive_hasDerivAt_local
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:36:29.322012+00:00
-- url     : https://prove2.me/submissions/42e6a104-457e-43d2-a5fa-abe91c62746d

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_deriv_eq_local

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

/-- An exponentially damped causal primitive admits a genuine pointwise
derivative witness under local interval integrability and continuity. -/
theorem solution
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume))
        (g x - w * (Real.exp (-w * x) *
          (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * g s ∂volume))) x := by
  intro x hx
  let f : ℝ → ℝ := fun s => Real.exp (w * s) * g s
  let G : ℝ → ℝ := fun y => ∫ s in Ioc (0 : ℝ) y, f s ∂volume
  have hAt : ContinuousAt f x := hCont.continuousAt (Ioi_mem_nhds hx)
  have hMeas : StronglyMeasurableAtFilter f (𝓝 x) volume :=
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hCont) x hx
  have hFTC : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, f s)
      (f x) x :=
    intervalIntegral.integral_hasDerivAt_right (hInt x hx) hMeas hAt
  have hG : HasDerivAt G (f x) x := by
    apply hFTC.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (intervalIntegral.integral_of_le hy.le).symm
  have hExpDiff : DifferentiableAt ℝ
      (fun y : ℝ => Real.exp (-w * y)) x := by
    fun_prop
  have hDiff : DifferentiableAt ℝ
      (fun y : ℝ => Real.exp (-w * y) * G y) x :=
    hExpDiff.mul hG.differentiableAt
  have hEq : deriv (fun y : ℝ => Real.exp (-w * y) * G y) x =
      g x - w * (Real.exp (-w * x) * G x) :=
    causal_exp_weighted_primitive_deriv_eq_local g w hInt hCont x hx
  change HasDerivAt (fun y : ℝ => Real.exp (-w * y) * G y)
    (g x - w * (Real.exp (-w * x) * G x)) x
  rw [← hEq]
  exact hDiff.hasDerivAt
