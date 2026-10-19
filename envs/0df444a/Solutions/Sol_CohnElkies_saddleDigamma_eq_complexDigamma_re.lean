-- Prove2me | solution 1 for CohnElkies.saddleDigamma_eq_complexDigamma_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/6a465d31-91ce-4ee7-9855-6c370516cd32

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
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 0 < x) :
    saddleDigamma x = (Complex.digamma (x : ℂ)).re := by
  have hΓ : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hcomplex :
      DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    apply Complex.differentiableAt_Gamma
    intro n h
    have hre := congrArg Complex.re h
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp at hre
    linarith
  have hreal :
      HasDerivAt Real.Gamma
        (deriv Complex.Gamma (x : ℂ)).re x := by
    have h := hcomplex.hasDerivAt.real_of_complex
    simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using! h
  unfold saddleDigamma
  rw [Real.deriv_log_comp_eq_logDeriv
    hreal.differentiableAt hΓ.ne',
    logDeriv_apply, hreal.deriv,
    Complex.digamma_def, logDeriv_apply,
    Complex.Gamma_ofReal, Complex.div_ofReal_re]
end CohnElkies
