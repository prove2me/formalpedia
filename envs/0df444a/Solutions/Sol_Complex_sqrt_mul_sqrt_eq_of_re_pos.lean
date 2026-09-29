-- Prove2me | solution 1 for Complex.sqrt_mul_sqrt_eq_of_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ef679a76-5c8d-5c38-9586-7b88651c1524

import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_sqrt_mul_sqrt_eq_of_re_pos

set_option autoImplicit false

noncomputable section

open Complex

open scoped Real

namespace DedekindEtaLaw

lemma sqrt_sq (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  have h := cpow_nat_inv_pow a two_ne_zero
  rw [Complex.sqrt]
  norm_num at h ⊢
  exact h

lemma sqrt_re (a : ℂ) : (Complex.sqrt a).re = √((‖a‖ + a.re) / 2) := by
  rw [Complex.sqrt]; exact cpow_inv_two_re a

lemma abs_sqrt_im (a : ℂ) : |(Complex.sqrt a).im| = √((‖a‖ - a.re) / 2) := by
  rw [Complex.sqrt]; exact abs_cpow_inv_two_im a

lemma sqrt_re_pos {a : ℂ} (ha : 0 < a.re) : 0 < (Complex.sqrt a).re := by
  rw [sqrt_re]
  apply Real.sqrt_pos_of_pos
  have := norm_nonneg a
  linarith

lemma abs_sqrt_im_lt_re {a : ℂ} (ha : 0 < a.re) : |(Complex.sqrt a).im| < (Complex.sqrt a).re := by
  rw [sqrt_re, abs_sqrt_im]
  apply Real.sqrt_lt_sqrt
  · have := re_le_norm a
    linarith
  · linarith

lemma eq_of_sq_eq_sq_of_re_pos {s t : ℂ} (h : s ^ 2 = t ^ 2) (hs : 0 < s.re) (ht : 0 < t.re) :
    s = t := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · exfalso
    rw [h, neg_re] at hs
    linarith

lemma neg_I_mul_re (ζ : ℂ) : (-I * ζ).re = ζ.im := by simp

lemma sqrt_neg_I_mul_re_pos {x : ℂ} (hx : |x.im| < x.re) : 0 < (Complex.sqrt (-I) * x).re := by
  rw [Complex.sqrt_neg_I, mul_assoc, re_ofReal_mul]
  have h2 : (0 : ℝ) < √(2⁻¹) := Real.sqrt_pos_of_pos (by norm_num)
  have : ((1 - I) * x).re = x.re + x.im := by simp [mul_re, sub_re, sub_im]
  rw [this]
  exact mul_pos h2 (by cases abs_lt.1 hx; linarith)

theorem sqrt_mul_sqrt_eq {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re)
    (h : u * v = -I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-I) * Complex.sqrt w := by
  apply eq_of_sq_eq_sq_of_re_pos
  · rw [mul_pow, mul_pow, sqrt_sq, sqrt_sq, sqrt_sq, sqrt_sq, h]
  · have h1 := abs_sqrt_im_lt_re hu
    have h2 := abs_sqrt_im_lt_re hv
    rw [mul_re]
    have : |(Complex.sqrt u).im * (Complex.sqrt v).im| < (Complex.sqrt u).re * (Complex.sqrt v).re := by
      rw [abs_mul]
      exact mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)
    have := (abs_lt.1 this).2
    linarith [(abs_lt.1 ‹|(Complex.sqrt u).im * (Complex.sqrt v).im| < _›).1]
  · exact sqrt_neg_I_mul_re_pos (abs_sqrt_im_lt_re hw)

end DedekindEtaLaw

end

theorem solution {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.sqrt u * Complex.sqrt v = Complex.sqrt (-Complex.I) * Complex.sqrt w :=
  DedekindEtaLaw.sqrt_mul_sqrt_eq hu hv hw h

end S_Complex_sqrt_mul_sqrt_eq_of_re_pos
end P2MW
export P2MW.S_Complex_sqrt_mul_sqrt_eq_of_re_pos (solution)
