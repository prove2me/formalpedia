-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_halfInteger
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:57:34.822038+00:00
-- url     : https://prove2.me/submissions/e529b96c-79ab-421c-8580-28ccccdde698

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
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

theorem h47_norm_gamma_neg (y : ℝ) :
    ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
  have h : -Complex.I * (y : ℂ) / 2 = (starRingEnd ℂ) (Complex.I * (y : ℂ) / 2) := by
    rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal,
      show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
    try ring
  rw [h, Complex.Gamma_conj, Complex.norm_conj]


theorem h47_norm_gamma_I_sq {x : ℝ} (hx : x ≠ 0) :
    ‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / (x * Real.sinh (Real.pi * x)) := by
  have hz : Complex.I * (x : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hx)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (Complex.I * (x : ℂ))
  have hsin : Complex.sin ((Real.pi : ℂ) * (Complex.I * (x : ℂ))) =
      (Real.sinh (Real.pi * x) : ℂ) * Complex.I := by
    rw [show (Real.pi : ℂ) * (Complex.I * (x : ℂ)) = ((Real.pi * x : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sin_mul_I, Complex.ofReal_sinh]
  have hone : 1 - Complex.I * (x : ℂ) = -(Complex.I * (x : ℂ)) + 1 := by ring
  rw [hone, Complex.Gamma_add_one _ (neg_ne_zero.2 hz), hsin] at hrefl
  have hconj : -(Complex.I * (x : ℂ)) = (starRingEnd ℂ) (Complex.I * (x : ℂ)) := by simp
  rw [hconj, Complex.Gamma_conj] at hrefl
  have hsh : Real.sinh (Real.pi * x) ≠ 0 := by
    intro h; rw [Real.sinh_eq_zero] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Real.pi_ne_zero h
    · exact hx h
  have hcz : (starRingEnd ℂ) (Complex.I * (x : ℂ)) ≠ 0 := by simpa using hz
  apply Complex.ofReal_injective
  have hn : ((‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 : ℝ) : ℂ) =
      Complex.Gamma (Complex.I * (x : ℂ)) * (starRingEnd ℂ) (Complex.Gamma (Complex.I * (x : ℂ))) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn]
  calc Complex.Gamma (Complex.I * (x : ℂ)) * (starRingEnd ℂ) (Complex.Gamma (Complex.I * (x : ℂ)))
      = (Complex.Gamma (Complex.I * (x : ℂ)) * ((starRingEnd ℂ) (Complex.I * (x : ℂ)) *
          (starRingEnd ℂ) (Complex.Gamma (Complex.I * (x : ℂ))))) /
          (starRingEnd ℂ) (Complex.I * (x : ℂ)) := by field_simp
    _ = (Real.pi : ℂ) / ((Real.sinh (Real.pi * x) : ℂ) * Complex.I) /
          (starRingEnd ℂ) (Complex.I * (x : ℂ)) := by rw [hrefl]
    _ = ((Real.pi / (x * Real.sinh (Real.pi * x)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_mul, div_div]
        congr 1
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        linear_combination (-(Real.sinh (Real.pi * x) : ℂ) * (x : ℂ)) * Complex.I_sq

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

theorem h47b_fact (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (Real.log ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖) := by
  unfold lowerGammaBoundaryLog
  have h2 : (((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2 =
      (((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2 = (1 / 2 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h47_norm_gamma_neg, h2, h47_gamma_shift, h3]
  have hpos : ∀ j ∈ Finset.range k, Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) ≠ 0 := by
    intro j _
    apply (Real.sqrt_pos.2 _).ne'
    have : (0:ℝ) < (j : ℝ) + 1 / 2 := by positivity
    nlinarith
  have hG : ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := m.cast_nonneg
    linarith
  rw [Real.log_mul hG (Finset.prod_ne_zero_iff.2 hpos), Real.log_prod hpos]
  ring

theorem h47b_coth {x : ℝ} (hx : x ≠ 0) :
    Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ -
        Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
  have hA := h47_norm_gamma_I_sq hx
  have hB := h47_norm_gamma_half_I_sq x
  have hp := Real.pi_pos
  have hxs : 0 < x * Real.sinh (Real.pi * x) := by
    rcases lt_or_gt_of_ne hx with h | h
    · have := Real.sinh_neg_iff.2 (by nlinarith : Real.pi * x < 0); nlinarith
    · have := Real.sinh_pos_iff.2 (by nlinarith : 0 < Real.pi * x); nlinarith
  have hch := Real.cosh_pos (Real.pi * x)
  have ha2 : ‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 ≠ 0 := by rw [hA]; positivity
  have hb2 : ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 ≠ 0 := by rw [hB]; positivity
  calc Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ -
        Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖
      = (1 / 2 : ℝ) * (Real.log (‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2) -
          Real.log (‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2)) := by
        rw [Real.log_pow, Real.log_pow]; push_cast; ring
    _ = (1 / 2 : ℝ) * Real.log (‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 /
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2) := by
        rw [Real.log_div ha2 hb2]
    _ = (1 / 2 : ℝ) * Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
        rw [hA, hB]
        congr 2
        unfold lowerCoth
        rcases lt_or_gt_of_ne hx with h | h
        · rw [abs_of_neg h, show Real.pi * -x = -(Real.pi * x) by ring, Real.cosh_neg, Real.sinh_neg]
          have : Real.sinh (Real.pi * x) ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hxs; exact lt_irrefl 0 hxs
          field_simp
        · rw [abs_of_pos h]
          have : Real.sinh (Real.pi * x) ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hxs; exact lt_irrefl 0 hxs
          field_simp

theorem solution
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) := by
  rw [h47b_fact k R hy]
  have hx : y / 2 ≠ 0 := div_ne_zero hy two_ne_zero
  have h1 : Complex.I * (y : ℂ) / 2 = Complex.I * ((y / 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2 = (1 / 2 : ℂ) + Complex.I * ((y / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h47b_coth hx, abs_div, abs_two, show Real.pi * (|y| / 2) = Real.pi * |y| / 2 by ring]

