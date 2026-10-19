-- Prove2me | solution 2 for CohnElkies.upperShortMargin_mul_exp_antitone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:14:29.44441+00:00
-- url     : https://prove2.me/submissions/7254234d-e0c3-463a-9601-39add265b6ea

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn
      (fun a : ℝ =>
        shortMargin ε a * Real.exp (ε * a))
      (Ici (0 : ℝ)) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun a : ℝ => shortMargin ε a * Real.exp (ε * a))
      (-(10 * ε) * Real.exp (ε * x) + shortMargin ε x * (Real.exp (ε * x) * ε)) x := by
    intro x
    have h1 : HasDerivAt (fun a : ℝ => shortMargin ε a) (-(10 * ε)) x := by
      unfold shortMargin
      have := (((hasDerivAt_id x).const_add 1).const_mul (10 * ε)).const_sub 1
      simpa using this
    have h2 : HasDerivAt (fun a : ℝ => Real.exp (ε * a)) (Real.exp (ε * x) * ε) x := by
      simpa using ((hasDerivAt_id x).const_mul ε).exp
    exact h1.mul h2
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact (continuous_iff_continuousAt.2 fun x => (hd x).continuousAt).continuousOn
  · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0:ℝ) < x := hx
    rw [(hd x).deriv]
    unfold shortMargin
    have he := Real.exp_pos (ε * x)
    nlinarith [mul_pos hε he, mul_pos (mul_pos hε hε) he, mul_pos (mul_pos (mul_pos hε hε) he) hx0]

