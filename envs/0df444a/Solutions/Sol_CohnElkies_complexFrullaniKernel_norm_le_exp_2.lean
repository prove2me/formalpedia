-- Prove2me | solution 2 for CohnElkies.complexFrullaniKernel_norm_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:30.299421+00:00
-- url     : https://prove2.me/submissions/4d736926-2b83-4d5d-a07f-ae6b48a85733

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
    (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖complexFrullaniKernel z w x‖ ≤
      ‖w - z‖ *
        Real.exp (-(min z.re w.re) * x) := by
  set m := min z.re w.re with hmdef
  let g : ℝ → ℂ := fun s => Complex.exp (-(z + (s:ℂ) * (w - z)) * x)
  have hg : ∀ s, HasDerivAt g (g s * (-(w - z) * x)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(z + (s:ℂ) * (w - z)) * x) (-(w - z) * x) s := by
      have := ((((hasDerivAt_id s).ofReal_comp).mul_const (w - z)).const_add z).neg.mul_const (x:ℂ)
      exact this.congr_deriv (by simp)
    exact h1.cexp
  have hbound : ∀ s ∈ Ico (0:ℝ) 1, ‖g s * (-(w - z) * x)‖ ≤ ‖w - z‖ * x * Real.exp (-m * x) := by
    intro s hs
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    have hre : (-(z + (s:ℂ) * (w - z)) * x).re = -((1 - s) * z.re + s * w.re) * x := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_im, Complex.add_im, Complex.mul_im, Complex.sub_im]
      ring
    rw [hre]
    have h1 : (1 - s) * m ≤ (1 - s) * z.re := mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith [hs.2])
    have h2 : s * m ≤ s * w.re := mul_le_mul_of_nonneg_left (min_le_right _ _) hs.1
    have : Real.exp (-((1 - s) * z.re + s * w.re) * x) ≤ Real.exp (-m * x) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (-((1 - s) * z.re + s * w.re) * x) * (‖w - z‖ * x)
        ≤ Real.exp (-m * x) * (‖w - z‖ * x) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (hg s).hasDerivWithinAt) hbound 1
    (right_mem_Icc.2 zero_le_one)
  unfold complexFrullaniKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, div_le_iff₀ hx]
  have e : Complex.exp (-z * x) - Complex.exp (-w * x) = -(g 1 - g 0) := by
    simp only [g]
    push_cast
    ring_nf
  rw [e, norm_neg]
  linarith

