-- Prove2me | solution 2 for CohnElkies.lowerWallis_complexEndpointPhase_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:41:09.05648+00:00
-- url     : https://prove2.me/submissions/ea21d2d2-b02a-4b2f-9de4-3e8afb253f18

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution (u : ℝ) :
    (1 + (-Complex.I * (u : ℂ)) *
      Complex.log (-Complex.I * (u : ℂ)) -
      ((-Complex.I * (u : ℂ)) + 1) *
        Complex.log ((-Complex.I * (u : ℂ)) + 1)).re =
          1 + lowerEndpointPhase (2 * u) := by
  have hz : (-Complex.I * (u : ℂ)).re = 0 := by simp
  have hzi : (-Complex.I * (u : ℂ)).im = -u := by simp
  have hw : (-Complex.I * (u : ℂ) + 1).re = 1 := by simp
  have hwi : (-Complex.I * (u : ℂ) + 1).im = -u := by simp
  have harg1 : u * Complex.arg (-Complex.I * (u : ℂ)) = -(Real.pi * |u| / 2) := by
    rcases lt_trichotomy u 0 with h | h | h
    · have : -Complex.I * (u : ℂ) = ((-u : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.arg_real_mul _ (by linarith), Complex.arg_I, abs_of_neg h]; ring
    · subst h; simp
    · have : -Complex.I * (u : ℂ) = ((u : ℝ) : ℂ) * (-Complex.I) := by ring
      rw [this, Complex.arg_real_mul _ h, Complex.arg_neg_I, abs_of_pos h]; ring
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have harg2 : Complex.arg (-Complex.I * (u : ℂ) + 1) = -Real.arctan u := by
    have : -Complex.I * (u : ℂ) + 1 = ((Real.sqrt (1 + u ^ 2) : ℝ) : ℂ) *
        (Complex.cos ((Real.arctan (-u) : ℝ) : ℂ) + Complex.sin ((Real.arctan (-u) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_arctan, Real.sin_arctan]
      apply Complex.ext <;> simp <;> field_simp
    rw [this, Complex.arg_real_mul _ hs, Complex.arg_cos_add_sin_mul_I, Real.arctan_neg]
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan (-u), Real.pi_pos]
    · linarith [Real.arctan_lt_pi_div_two (-u), Real.pi_pos]
  have hn : ‖-Complex.I * (u : ℂ) + 1‖ = Real.sqrt (1 + u ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, hw, hwi]; congr 1; ring
  have hua : u * Real.arctan u = |u| * Real.arctan |u| := by
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.arctan_neg]; ring
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.one_re, hz, hzi, hw, hwi,
    Complex.log_re, Complex.log_im, harg2, hn]
  unfold lowerEndpointPhase
  rw [Real.log_sqrt (by positivity)]
  have h2 : |2 * u| = 2 * |u| := by rw [abs_mul]; norm_num
  rw [h2]
  have h3 : 2 * |u| / 2 = |u| := by ring
  rw [h3]
  have h4 : (2 * u) ^ 2 / 4 = u ^ 2 := by ring
  rw [h4]
  nlinarith [harg1, hua]

