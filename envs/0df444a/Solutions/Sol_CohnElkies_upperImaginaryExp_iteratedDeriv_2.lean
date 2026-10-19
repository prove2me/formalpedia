-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:58:01.178333+00:00
-- url     : https://prove2.me/submissions/c069424c-fe92-41fe-b95b-70dbdbe1a835

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology


theorem solution
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n upperImaginaryExp x =
      Complex.I ^ n * upperImaginaryExp x := by
  have hd : ∀ y : ℝ, HasDerivAt upperImaginaryExp (Complex.I * upperImaginaryExp y) y := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) (Complex.I * 1) y :=
      (hasDerivAt_id (y : ℂ)).comp_ofReal.const_mul Complex.I
    have := h1.cexp
    unfold upperImaginaryExp
    convert this using 1
    ring
  have hD : deriv upperImaginaryExp = fun y => Complex.I * upperImaginaryExp y :=
    funext fun y => (hd y).deriv
  have key : ∀ m : ℕ, iteratedDeriv m upperImaginaryExp = fun y => Complex.I ^ m * upperImaginaryExp y := by
    intro m
    induction m with
    | zero => funext y; simp
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      rw [deriv_const_mul _ (hd y).differentiableAt, hD]
      ring
  rw [key]

