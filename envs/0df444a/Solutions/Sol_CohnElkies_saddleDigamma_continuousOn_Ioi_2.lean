-- Prove2me | solution 2 for CohnElkies.saddleDigamma_continuousOn_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:58:16.939107+00:00
-- url     : https://prove2.me/submissions/7e62e146-03fa-48e5-9d0a-3ec78045667e

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


theorem solution :
    ContinuousOn saddleDigamma (Ioi (0 : ℝ)) := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -m := by
    intro z hz m h; rw [h] at hz; simp at hz <;> linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have hEq : EqOn saddleDigamma (fun x : ℝ => (deriv Complex.Gamma (x:ℂ)).re / Real.Gamma x) (Ioi 0) := by
    intro x hx
    have hx' : (0:ℝ) < (x:ℂ).re := by simpa using hx
    have h1 := (Complex.differentiableAt_Gamma _ (hne _ hx')).hasDerivAt.real_of_complex
    have h2 : HasDerivAt Real.Gamma (deriv Complex.Gamma (x:ℂ)).re x := by
      convert h1 using 1; funext y; rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    have h3 := h2.log (Real.Gamma_pos_of_pos hx).ne'
    unfold saddleDigamma
    exact h3.deriv
  refine ContinuousOn.congr ?_ hEq
  refine ContinuousOn.div ?_ Real.differentiableOn_Gamma_Ioi.continuousOn
    (fun x hx => (Real.Gamma_pos_of_pos hx).ne')
  refine Complex.continuous_re.comp_continuousOn
    ((hd.deriv hU).continuousOn.comp Complex.continuous_ofReal.continuousOn ?_)
  intro x hx; simpa using hx

