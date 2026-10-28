-- Prove2me | solution 1 for AvramDividend.Classical.excursion_integrated_tilted_scale_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:34:21.919737+00:00
-- url     : https://prove2.me/submissions/bd97dafd-4d05-46ff-9a8d-55c35336f245

import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter intervalIntegral

theorem solution
    (W V : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi (0 : ℝ)))
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    MonotoneOn V (Ioi (0 : ℝ)) := by
  have hWder := excursion_integral_scale_derivative W φ μ hcont hexp
  have hVder : ∀ x : ℝ, 0 < x →
      HasDerivAt V (V x * μ.real (Ici x)) x := by
    intro x hx
    have hf0 : HasDerivAt (fun y : ℝ => (-φ) * y) (-φ) x := by
      convert ((hasDerivAt_id x).const_mul (-φ)) using 1 <;>
        (first | rfl | ring)
    have he0 : HasDerivAt (fun y : ℝ => Real.exp ((-φ) * y))
        (Real.exp ((-φ) * x) * (-φ)) x := by
      exact (Real.hasDerivAt_exp ((-φ) * x)).comp x hf0
    have he : HasDerivAt (fun y : ℝ => Real.exp (-(φ * y)))
        (Real.exp (-(φ * x)) * (-φ)) x := by
      simpa only [neg_mul] using he0
    have hprod := he.mul (hWder x hx)
    have hnear : ∀ᶠ y : ℝ in nhds x, 0 < y :=
      isOpen_Ioi.mem_nhds hx
    have heq : V =ᶠ[nhds x]
        (fun y : ℝ => Real.exp (-(φ * y)) * W y) := by
      filter_upwards [hnear] with y hy
      exact hV y hy
    have hh := hprod.congr_of_eventuallyEq heq
    have hderiv_eq :
        (Real.exp (-(φ * x)) * (-φ)) * W x +
          Real.exp (-(φ * x)) * (W x * (φ + μ.real (Ici x))) =
          V x * μ.real (Ici x) := by
      rw [hV x hx]
      ring
    rw [hderiv_eq] at hh
    exact hh
  have hVcont : ContinuousOn V (Ioi (0 : ℝ)) := by
    intro x hx
    exact (hVder x hx).continuousAt.continuousWithinAt
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ)) hVcont
  · intro x hx
    exact (hVder x (by simpa using hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa using hx
    have hval : 0 < V x := by
      rw [hV x hx']
      exact mul_pos (Real.exp_pos _) (hWpos x hx')
    rw [(hVder x hx').deriv]
    exact mul_nonneg (le_of_lt hval) ENNReal.toReal_nonneg
