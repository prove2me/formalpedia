-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_iteratedDerivWithin_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:28.653236+00:00
-- url     : https://prove2.me/submissions/4f7b3783-3ed0-4876-a338-15ea0732a664

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
theorem h47_uie_hasDerivAt (y : ℝ) :
    HasDerivAt CohnElkies.upperImaginaryExp (Complex.I * CohnElkies.upperImaginaryExp y) y := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) (Complex.I * 1) y :=
    (hasDerivAt_id (y : ℂ)).comp_ofReal.const_mul Complex.I
  have := h1.cexp
  unfold CohnElkies.upperImaginaryExp
  convert this using 1
  ring
theorem h47_uie_iter (m : ℕ) : iteratedDeriv m CohnElkies.upperImaginaryExp =
    fun y => Complex.I ^ m * CohnElkies.upperImaginaryExp y := by
  have hD : deriv CohnElkies.upperImaginaryExp = fun y => Complex.I * CohnElkies.upperImaginaryExp y :=
    funext fun y => (h47_uie_hasDerivAt y).deriv
  induction m with
  | zero => funext y; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [deriv_const_mul _ (h47_uie_hasDerivAt y).differentiableAt, hD]
    ring
theorem h47_uie_norm (y : ℝ) : ‖CohnElkies.upperImaginaryExp y‖ = 1 := by
  unfold CohnElkies.upperImaginaryExp
  rw [Complex.norm_exp]
  simp

theorem solution
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (n : ℕ) :
    iteratedDerivWithin n upperImaginaryExp (Icc a b) x =
      Complex.I ^ n * upperImaginaryExp x := by
  have hcd : ContDiff ℝ (⊤ : WithTop ℕ∞) upperImaginaryExp := by
    unfold upperImaginaryExp; exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) (hcd.contDiffAt.of_le le_top) hx,
    h47_uie_iter]

