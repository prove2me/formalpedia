-- Prove2me | solution 2 for CohnElkies.upperPositiveHalfGamma_scaled_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:45.843793+00:00
-- url     : https://prove2.me/submissions/7935ae98-580f-43a2-8df5-03409a59b3a8

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
theorem h47_gamma_shift (n : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ =
      ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ *
        ∏ j ∈ Finset.range n, Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ n := n.cast_nonneg
      linarith
    rw [show ((((n + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) =
      ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hs, norm_mul, ih, Finset.prod_range_succ]
    have hn : ‖(((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)‖ =
        Real.sqrt (((n : ℝ) + 1 / 2) ^ 2 + t ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      simp
      ring
    rw [hn]
    ring

theorem h47_norm_gamma_half_I_sq (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * x) := by
  have hrefl := Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + Complex.I * (x : ℂ))
  have hsin : Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (x : ℂ))) =
      (Real.cosh (Real.pi * x) : ℂ) := by
    rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * (x : ℂ)) =
      ((Real.pi * x : ℝ) : ℂ) * Complex.I + (Real.pi : ℂ) / 2 by push_cast; ring,
      Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  have hconj : 1 - ((1 / 2 : ℂ) + Complex.I * (x : ℂ)) =
      (starRingEnd ℂ) ((1 / 2 : ℂ) + Complex.I * (x : ℂ)) := by
    apply Complex.ext <;> simp <;> norm_num
  rw [hsin, hconj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hrefl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_div, Complex.ofReal_cosh]
  push_cast at hrefl ⊢
  exact hrefl

theorem solution
    (n : ℕ) (x : ℝ) :
    Real.Gamma ((n : ℝ) + 1 / 2) ^ 2 ≤
      ‖Complex.Gamma
        (((((n : ℝ) + 1 / 2) : ℝ) : ℂ) +
          Complex.I * (x : ℂ))‖ ^ 2 *
        Real.cosh (Real.pi * x) := by
  have hA := h47_gamma_shift n x
  have hB := h47_gamma_shift n 0
  have hR : Real.Gamma ((n : ℝ) + 1 / 2) =
      ‖Complex.Gamma ((((n : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ))‖ := by
    rw [Complex.ofReal_zero, mul_zero, add_zero, Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]
  rw [hR, hB, hA, mul_pow, mul_pow, h47_norm_gamma_half_I_sq x, h47_norm_gamma_half_I_sq 0,
    mul_zero, Real.cosh_zero, div_one]
  have hc := Real.cosh_pos (Real.pi * x)
  have he : Real.pi / Real.cosh (Real.pi * x) *
      (∏ j ∈ Finset.range n, Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + x ^ 2)) ^ 2 * Real.cosh (Real.pi * x) =
      Real.pi * (∏ j ∈ Finset.range n, Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + x ^ 2)) ^ 2 := by
    rw [mul_right_comm, div_mul_cancel₀ _ hc.ne']
  rw [he]
  apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
  apply pow_le_pow_left₀ (Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _)
  apply Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _)
  intro j _
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg x]

