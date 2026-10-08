-- Prove2me | solution 1 for AvramDividend.Classical.exp_tilt_deriv_growth_of_positive_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T18:27:50.189093+00:00
-- url     : https://prove2.me/submissions/cdb83bad-2e34-46ac-a74c-b4b26c789ef1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Filter Set
open scoped ENNReal

theorem solution (φ c : ℝ) (hφ : 0 < φ) (hc : 0 < c) (V : ℝ → ℝ)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x)
    (hderiv : ∀ x : ℝ, 0 < x → 0 ≤ deriv V x)
    (hbound : ∀ᶠ x : ℝ in Filter.atTop, c ≤ V x) :
    Filter.Tendsto (deriv (fun x : ℝ => Real.exp (φ * x) * V x))
      Filter.atTop Filter.atTop := by
  have hfactor (x : ℝ) (hx : 0 < x) :
      deriv (fun t : ℝ => Real.exp (φ * t) * V t) x =
        (Real.exp (φ * x) * φ) * V x +
          Real.exp (φ * x) * deriv V x := by
    have he : HasDerivAt (fun t : ℝ => Real.exp (φ * t))
        (Real.exp (φ * x) * φ) x :=
      (hasDerivAt_const_mul (x := x) φ).exp
    have hv : HasDerivAt V (deriv V x) x :=
      (hdiff x hx).hasDerivAt
    exact (he.mul hv).deriv
  have hlin : Filter.Tendsto (fun x : ℝ => φ * x)
      Filter.atTop Filter.atTop :=
    (tendsto_const_mul_atTop_of_pos hφ).2 tendsto_id
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (φ * x))
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hlower : Filter.Tendsto
      (fun x : ℝ => (φ * c) * Real.exp (φ * x))
      Filter.atTop Filter.atTop :=
    (tendsto_const_mul_atTop_of_pos (mul_pos hφ hc)).2 hexp
  have hcomp : (fun x : ℝ => (φ * c) * Real.exp (φ * x)) ≤ᶠ[Filter.atTop]
      (fun x : ℝ => deriv (fun t : ℝ => Real.exp (φ * t) * V t) x) := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hxV hx
    have hexp0 : 0 ≤ Real.exp (φ * x) :=
      (Real.exp_pos _).le
    have hφexp : 0 ≤ Real.exp (φ * x) * φ :=
      mul_nonneg hexp0 hφ.le
    have hterm : 0 ≤ Real.exp (φ * x) * deriv V x :=
      mul_nonneg hexp0 (hderiv x hx)
    calc
      (φ * c) * Real.exp (φ * x) =
          (Real.exp (φ * x) * φ) * c := by ring
      _ ≤ (Real.exp (φ * x) * φ) * V x :=
        mul_le_mul_of_nonneg_left hxV hφexp
      _ ≤ deriv (fun t : ℝ => Real.exp (φ * t) * V t) x := by
        rw [hfactor x hx]
        exact le_add_of_nonneg_right hterm
  exact tendsto_atTop_mono' Filter.atTop hcomp hlower
