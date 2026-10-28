-- Prove2me | solution 1 for AvramDividend.Classical.monotone_C1_kernel_derivative_primitive_from_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:25:13.968904+00:00
-- url     : https://prove2.me/submissions/cb45a064-f65a-46b4-91b6-dcf2df89883e

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-- A monotone kernel's positive-time derivative recovers its zero-origin values. -/
theorem solution
    (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (deriv g) volume 0 x ∧
      (∫ t in (0 : ℝ)..x, deriv g t) = g x := by
  intro x hx
  have hu : uIcc (0 : ℝ) x = Icc 0 x := uIcc_of_le hx.le
  have huo : uIoo (0 : ℝ) x = Ioo 0 x := uIoo_of_le hx.le
  have hmono : MonotoneOn g (uIcc (0 : ℝ) x) := by
    rw [hu]
    exact hgmono.mono (by intro y hy; exact hy.1)
  have hcont : ContinuousOn g (uIcc (0 : ℝ) x) := by
    rw [hu]
    exact hgcont.mono (by intro y hy; exact hy.1)
  have hint : IntervalIntegrable (deriv g) volume 0 x :=
    hmono.intervalIntegrable_deriv
  have hdiff : ∀ y ∈ uIoo (0 : ℝ) x, DifferentiableAt ℝ g y := by
    intro y hy
    rw [huo] at hy
    have hC1y : ContDiffAt ℝ 1 g y :=
      hgC1.contDiffAt (isOpen_Ioi.mem_nhds hy.1)
    exact hC1y.differentiableAt (by norm_num)
  refine ⟨hint, ?_⟩
  have heq : (∫ t in (0 : ℝ)..x, deriv g t) = g x - g 0 :=
    intervalIntegral.integral_deriv_eq_sub_uIoo hcont hdiff hint
  simpa only [hg0, sub_zero] using heq
