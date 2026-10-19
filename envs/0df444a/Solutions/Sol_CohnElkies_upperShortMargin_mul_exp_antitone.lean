-- Prove2me | solution 1 for CohnElkies.upperShortMargin_mul_exp_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/9be26534-7fd5-45e7-8965-8f6b47189cf5

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
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn
      (fun a : ℝ =>
        shortMargin ε a * Real.exp (ε * a))
      (Ici (0 : ℝ)) := by
  let f : ℝ → ℝ := fun a =>
    shortMargin ε a * Real.exp (ε * a)
  have hderiv (a : ℝ) :
      HasDerivAt f
        (ε * Real.exp (ε * a) *
          (shortMargin ε a - 10)) a := by
    have hmargin : HasDerivAt
        (fun x : ℝ => shortMargin ε x)
        (-(10 * ε)) a := by
      have h :=
        (hasDerivAt_const a (1 : ℝ)).sub
          ((hasDerivAt_const a (10 * ε)).mul
            ((hasDerivAt_const a (1 : ℝ)).add
              (hasDerivAt_id a)))
      convert! h using 1; simp [Pi.add_apply, id]
    have hexp : HasDerivAt
        (fun x : ℝ => Real.exp (ε * x))
        (Real.exp (ε * a) * ε) a := by
      convert! ((hasDerivAt_id a).const_mul ε).exp
        using 1; simp [id]
    have h := hmargin.mul hexp
    convert! h using 1; simp; ring
  apply antitoneOn_of_deriv_nonpos
    (convex_Ici (0 : ℝ))
  · have hc : Continuous f := by
      try dsimp [f]
      unfold shortMargin
      fun_prop
    exact hc.continuousOn
  · intro a ha
    exact (hderiv a).differentiableAt.differentiableWithinAt
  · intro a ha
    rw [(hderiv a).deriv]
    have ha0 : 0 ≤ a := by
      have h := interior_subset ha
      exact h
    have hmargin : shortMargin ε a ≤ 1 := by
      unfold shortMargin
      nlinarith [mul_nonneg hε.le
        (show 0 ≤ 1 + a by linarith)]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hε.le (Real.exp_pos _).le)
      (by linarith)
end CohnElkies
