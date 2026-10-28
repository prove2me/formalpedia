-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_resolvent_convolution_integrable_of_tilted_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:59:00.478644+00:00
-- url     : https://prove2.me/submissions/827488df-904a-4017-add5-acb6bea254c5

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_killed_resolvent_kernel_nonneg_full_halfline

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- The scale convolution is integrable when dominated by its Laplace term. -/
theorem solution
    (θ : ℝ) (Wq Wqp : ℝ → ℝ)
    (hmono : MonotoneOn
      (fun z : ℝ => Real.exp (-(θ * z)) * Wqp z) (Ici (0 : ℝ)))
    (hWq_nonneg : ∀ z : ℝ, 0 ≤ z → 0 ≤ Wq z)
    (hWqp_nonneg : ∀ z : ℝ, 0 ≤ Wqp z)
    (hnegative : ∀ z : ℝ, z < 0 → Wqp z = 0)
    (x : ℝ) (hx : 0 ≤ x)
    (hfirst : IntegrableOn
      (fun y : ℝ => Wq y * (Real.exp (-(θ * y)) * Wqp x))
      (Ioi (0 : ℝ)))
    (hmeas : AEStronglyMeasurable
      (fun y : ℝ => Wq y * Wqp (x - y))
      (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun y : ℝ => Wq y * Wqp (x - y)) (Ioi (0 : ℝ)) := by
  apply Integrable.mono_nonneg hfirst hmeas
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hWy : 0 ≤ Wq y := hWq_nonneg y (le_of_lt hy)
    exact mul_nonneg hWy (hWqp_nonneg (x - y))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hWy : 0 ≤ Wq y := hWq_nonneg y (le_of_lt hy)
    have hker : 0 ≤ Real.exp (-(θ * y)) * Wqp x - Wqp (x - y) :=
      chat04_killed_resolvent_kernel_nonneg_full_halfline
        θ Wqp hmono (fun z _ => hWqp_nonneg z)
        hnegative x y hx (le_of_lt hy)
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hker) hWy
