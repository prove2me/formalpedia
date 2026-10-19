-- Prove2me | solution 2 for CohnElkies.saddleDigamma_eq_complexDigamma_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:01.792382+00:00
-- url     : https://prove2.me/submissions/0993852f-d4c7-43e1-8ff1-9db7a4c67520

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {x : ℝ} (hx : 0 < x) :
    saddleDigamma x = (Complex.digamma (x : ℂ)).re := by
  have hne : ∀ m : ℕ, (x : ℂ) ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hc : HasDerivAt Complex.Gamma (deriv Complex.Gamma (x : ℂ)) (x : ℂ) :=
    (Complex.differentiableAt_Gamma _ hne).hasDerivAt
  have hr := hc.real_of_complex
  have hfun : (fun r : ℝ => (Complex.Gamma (r : ℂ)).re) = Real.Gamma := by
    funext r; rw [Complex.Gamma_ofReal]; simp
  rw [hfun] at hr
  have hG := Real.Gamma_pos_of_pos hx
  have hl := hr.log hG.ne'
  unfold saddleDigamma
  rw [show (Real.log ∘ Real.Gamma) = fun y => Real.log (Real.Gamma y) from rfl, hl.deriv]
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re]

