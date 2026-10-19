-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_cubicIntegral_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:22.450908+00:00
-- url     : https://prove2.me/submissions/35d3ea33-d920-4bb6-ae42-e6e867b6edda

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
    {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in (0 : ℝ)..x,
        ((x - t) ^ 2 / 2 : ℝ) •
          iteratedDeriv 3 upperImaginaryExp t‖ ≤
      x ^ 3 / 6 := by
  have hb : ∀ t : ℝ, ‖((x - t) ^ 2 / 2 : ℝ) • iteratedDeriv 3 upperImaginaryExp t‖ = (x - t) ^ 2 / 2 := by
    intro t
    rw [norm_smul, h47_uie_iter, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, h47_uie_norm,
      mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖∫ t in (0 : ℝ)..x, ((x - t) ^ 2 / 2 : ℝ) • iteratedDeriv 3 upperImaginaryExp t‖
      ≤ ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 :=
        intervalIntegral.norm_integral_le_of_norm_le hx
          (Filter.Eventually.of_forall fun t _ => (hb t).le) (by apply Continuous.intervalIntegrable; fun_prop)
    _ = x ^ 3 / 6 := by
        rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ 2 / 2) x]
        simp only [sub_self, sub_zero]
        rw [intervalIntegral.integral_div, integral_pow]
        ring

