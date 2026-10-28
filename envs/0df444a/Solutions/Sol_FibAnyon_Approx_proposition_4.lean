-- Prove2me | solution 1 for FibAnyon.Approx.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T04:19:10.29526+00:00
-- url     : https://prove2.me/submissions/6d352b9d-e8fe-496b-9fb0-6aa3992836ae

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace Aux_FAp4
open FibAnyon.Approx

lemma w10_eq : w10 = Complex.exp (((Real.pi / 5 : ℝ) : ℂ) * Complex.I) := by
  unfold w10; congr 1; push_cast; ring

lemma w10_pow (k : ℕ) : w10 ^ k = Complex.exp ((((k : ℝ) * (Real.pi / 5) : ℝ) : ℂ) * Complex.I) := by
  rw [w10_eq, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma toC_re (x : ZOmega) : x.toC.re = x.a + x.b * Real.cos (Real.pi / 5) +
    x.c * Real.cos (2 * (Real.pi / 5)) + x.d * Real.cos (3 * (Real.pi / 5)) := by
  unfold ZOmega.toC
  rw [w10_pow 2, w10_pow 3, w10_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  push_cast
  ring

lemma toC_im (x : ZOmega) : x.toC.im = x.b * Real.sin (Real.pi / 5) +
    x.c * Real.sin (2 * (Real.pi / 5)) + x.d * Real.sin (3 * (Real.pi / 5)) := by
  unfold ZOmega.toC
  rw [w10_pow 2, w10_pow 3, w10_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, Complex.ofReal_im,
    Complex.ofReal_re]
  push_cast
  ring

lemma gauss_eq (a b c d : ℤ) : gaussG ⟨a, b, c, d⟩ =
    ((2*a^2+2*b^2+2*c^2+2*d^2+a*b-a*c+a*d+b*c-b*d+c*d : ℤ) : ℝ) := by
  unfold gaussG
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    toC_re, toC_im, toC_re, toC_im]
  simp only [ZOmega.bullet]
  rw [Real.cos_two_mul, Real.sin_two_mul, Real.cos_three_mul, Real.sin_three_mul]
  push_cast
  set co := Real.cos (Real.pi / 5) with hco
  set si := Real.sin (Real.pi / 5) with hsi
  have hs : si ^ 2 + co ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hc : 4 * co ^ 2 - 2 * co - 1 = 0 := by
    rw [hco, Real.cos_pi_div_five]
    have := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
    linear_combination (1/4 : ℝ) * this
  linear_combination (16*(b:ℝ)^2*co^4 - 16*(b:ℝ)^2*co^2*si^2 - 8*(b:ℝ)^2*co^2 + 16*(b:ℝ)^2*si^4 - 8*(b:ℝ)^2*si^2 + 2*(b:ℝ)^2 - 8*(b:ℝ)*(c:ℝ)*co^2 + 4*(b:ℝ)*(c:ℝ)*co + 8*(b:ℝ)*(c:ℝ)*si^2 + 2*(b:ℝ)*(c:ℝ) - 32*(b:ℝ)*(d:ℝ)*co^4 + 16*(b:ℝ)*(d:ℝ)*co^3 + 32*(b:ℝ)*(d:ℝ)*co^2*si^2 + 16*(b:ℝ)*(d:ℝ)*co^2 - 16*(b:ℝ)*(d:ℝ)*co*si^2 - 4*(b:ℝ)*(d:ℝ)*co - 32*(b:ℝ)*(d:ℝ)*si^4 + 16*(b:ℝ)*(d:ℝ)*si^2 - 2*(b:ℝ)*(d:ℝ) + 4*(c:ℝ)^2*co^2 + (c:ℝ)^2 + 16*(c:ℝ)*(d:ℝ)*co^3 + 8*(c:ℝ)*(d:ℝ)*co^2 - 16*(c:ℝ)*(d:ℝ)*co*si^2 - 8*(c:ℝ)*(d:ℝ)*co - 8*(c:ℝ)*(d:ℝ)*si^2 + 32*(d:ℝ)^2*co^4 - 16*(d:ℝ)^2*co^3 - 32*(d:ℝ)^2*co^2*si^2 - 4*(d:ℝ)^2*co^2 + 16*(d:ℝ)^2*co*si^2 + 32*(d:ℝ)^2*si^4 - 24*(d:ℝ)^2*si^2 + (d:ℝ)^2) * hs + (2*(a:ℝ)*(b:ℝ)*co + (a:ℝ)*(b:ℝ) + (a:ℝ)*(c:ℝ) + (a:ℝ)*(d:ℝ) - (b:ℝ)*(c:ℝ) + 2*(b:ℝ)*(d:ℝ)*co + (b:ℝ)*(d:ℝ) + (c:ℝ)*(d:ℝ) - 2*(d:ℝ)^2*co + (d:ℝ)^2) * hc


lemma bnd2 (a : ℤ) (h : a ^ 2 ≤ 4) : -2 ≤ a ∧ a ≤ 2 := by
  constructor <;> nlinarith [sq_nonneg (a + 2), sq_nonneg (a - 2)]

lemma bnd1 (a : ℤ) (h : a ^ 2 ≤ 2) : -1 ≤ a ∧ a ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]

lemma enum2 (a b c d : ℤ) (ha : -2 ≤ a ∧ a ≤ 2) (hb : -2 ≤ b ∧ b ≤ 2) (hc : -2 ≤ c ∧ c ≤ 2)
    (hd : -2 ≤ d ∧ d ≤ 2)
    (hQ : 2*a^2+2*b^2+2*c^2+2*d^2+a*b-a*c+a*d+b*c-b*d+c*d = 2) :
    ∃ k : ℕ, k < 10 ∧ (⟨a, b, c, d⟩ : ZOmega) = ZOmega.w.pow k := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    norm_num at hQ <;>
    first
      | exact ⟨0, by norm_num, by decide⟩
      | exact ⟨1, by norm_num, by decide⟩
      | exact ⟨2, by norm_num, by decide⟩
      | exact ⟨3, by norm_num, by decide⟩
      | exact ⟨4, by norm_num, by decide⟩
      | exact ⟨5, by norm_num, by decide⟩
      | exact ⟨6, by norm_num, by decide⟩
      | exact ⟨7, by norm_num, by decide⟩
      | exact ⟨8, by norm_num, by decide⟩
      | exact ⟨9, by norm_num, by decide⟩

lemma enum1 (a b c d : ℤ) (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1) (hc : -1 ≤ c ∧ c ≤ 1)
    (hd : -1 ≤ d ∧ d ≤ 1)
    (hQ : 2*a^2+2*b^2+2*c^2+2*d^2+a*b-a*c+a*d+b*c-b*d+c*d = 1) : False := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    norm_num at hQ

lemma key2 (a b c d : ℤ) :
    2 * (2*a^2+2*b^2+2*c^2+2*d^2+a*b-a*c+a*d+b*c-b*d+c*d) =
      (a^2+b^2+c^2+d^2) + ((a+b)^2 + (a-c)^2 + (a+d)^2 + (b+c)^2 + (b-d)^2 + (c+d)^2) := by
  ring

end Aux_FAp4

open FibAnyon.Approx Aux_FAp4 in
theorem solution (x : ZOmega) :
    (∃ n : ℤ, gaussG x = n) ∧
    (gaussG x = 0 → x = 0) ∧
    (gaussG x = 2 → ∃ k : ℕ, k < 10 ∧ x = ZOmega.w.pow k) ∧
    (gaussG x = 0 ∨ gaussG x = 2 ∨ 3 ≤ gaussG x) ∧
    gaussG x ≤ (5/2 : ℝ) *
      ((x.a:ℝ)^2 + (x.b:ℝ)^2 + (x.c:ℝ)^2 + (x.d:ℝ)^2) := by
  obtain ⟨a, b, c, d⟩ := x
  have hG := gauss_eq a b c d
  have hk := key2 a b c d
  set Q : ℤ := 2*a^2+2*b^2+2*c^2+2*d^2+a*b-a*c+a*d+b*c-b*d+c*d with hQ
  have p1 := sq_nonneg (a+b)
  have p2 := sq_nonneg (a-c)
  have p3 := sq_nonneg (a+d)
  have p4 := sq_nonneg (b+c)
  have p5 := sq_nonneg (b-d)
  have p6 := sq_nonneg (c+d)
  have qa := sq_nonneg a
  have qb := sq_nonneg b
  have qc := sq_nonneg c
  have qd := sq_nonneg d
  refine ⟨⟨Q, hG⟩, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [hG] at h0
    have hQ0 : Q = 0 := by exact_mod_cast h0
    have ha : a ^ 2 = 0 := by linarith
    have hb : b ^ 2 = 0 := by linarith
    have hc : c ^ 2 = 0 := by linarith
    have hd : d ^ 2 = 0 := by linarith
    rw [pow_eq_zero_iff two_ne_zero] at ha hb hc hd
    subst ha hb hc hd
    rfl
  · intro h2
    rw [hG] at h2
    have hQ2 : Q = 2 := by exact_mod_cast h2
    exact enum2 a b c d (bnd2 a (by linarith)) (bnd2 b (by linarith)) (bnd2 c (by linarith))
      (bnd2 d (by linarith)) hQ2
  · rw [hG]
    have hne1 : Q ≠ 1 := by
      intro hQ1
      exact enum1 a b c d (bnd1 a (by linarith)) (bnd1 b (by linarith)) (bnd1 c (by linarith))
        (bnd1 d (by linarith)) hQ1
    have hQnn : 0 ≤ Q := by linarith
    rcases lt_trichotomy Q 2 with h | h | h
    · left
      have : Q = 0 := by omega
      rw [this]; norm_num
    · right; left; rw [h]; norm_num
    · right; right
      have : (3 : ℤ) ≤ Q := by omega
      exact_mod_cast this
  · rw [hG]
    have h5 : 2 * Q = 5 * (a^2+b^2+c^2+d^2) - (a - b + c - d)^2 := by rw [hQ]; ring
    have : 2 * Q ≤ 5 * (a^2+b^2+c^2+d^2) := by linarith [sq_nonneg (a - b + c - d)]
    have h' : (2 : ℝ) * Q ≤ 5 * ((a:ℝ)^2 + (b:ℝ)^2 + (c:ℝ)^2 + (d:ℝ)^2) := by exact_mod_cast this
    show (Q : ℝ) ≤ 5 / 2 * ((a:ℝ)^2 + (b:ℝ)^2 + (c:ℝ)^2 + (d:ℝ)^2)
    linarith
