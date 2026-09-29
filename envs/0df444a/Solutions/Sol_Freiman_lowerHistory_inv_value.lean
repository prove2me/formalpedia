-- Prove2me | solution 1 for Freiman.lowerHistory_inv_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T17:19:09.271316+00:00
-- url     : https://prove2.me/submissions/0ba5ed3b-0756-4fc4-90a6-c1a037cd3f56

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

namespace Freiman

-- certFieldVal is the ℚ-algebra hom ℚ(√3,√7) → ℝ on the four-coordinate model.
lemma certFieldVal_add' (x y : CertField) :
    certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y := by
  simp only [certFieldVal, certFieldAdd]
  push_cast
  ring

lemma certFieldVal_scale' (q : ℚ) (x : CertField) :
    certFieldVal (certFieldScale q x) = (q : ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]
  push_cast
  ring

lemma certFieldVal_mul' (x y : CertField) :
    certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y := by
  have h21 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by
    rw [show (21:ℝ) = 3*7 by norm_num, Real.sqrt_mul (by norm_num)]
  have h3' : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h7' : (Real.sqrt 7)^2 = 7 := Real.sq_sqrt (by norm_num)
  simp only [certFieldVal, certFieldMul, h21]
  push_cast
  ring_nf
  rw [h3', h7']
  ring

-- 1 and √3 are linearly independent over ℚ.
lemma rat_add_rat_mul_sqrt3_eq_zero (u v : ℚ)
    (h : (u:ℝ) + (v:ℝ) * Real.sqrt 3 = 0) : u = 0 ∧ v = 0 := by
  have hirr : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
  by_cases hv : v = 0
  · rw [hv] at h
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, hv⟩
  · exfalso
    have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv
    have hsqrt : Real.sqrt 3 = ((-u/v : ℚ) : ℝ) := by
      push_cast
      rw [eq_div_iff hvR]
      linarith
    exact hirr.ne_rat (-u/v) hsqrt

lemma irrational_sqrt7 : Irrational (Real.sqrt 7) := by
  simpa using (irrational_sqrt_natCast_iff (n := 7)).mpr (by norm_num : ¬ IsSquare (7:ℕ))

lemma irrational_sqrt21 : Irrational (Real.sqrt 21) := by
  simpa using (irrational_sqrt_natCast_iff (n := 21)).mpr (by norm_num : ¬ IsSquare (21:ℕ))

-- √7 does not lie in ℚ(√3); this is the number-theoretic input for the inverse.
lemma sqrt7_ne_rat_add_rat_mul_sqrt3 (r s : ℚ) :
    Real.sqrt 7 ≠ (r:ℝ) + (s:ℝ) * Real.sqrt 3 := by
  intro h
  have hirr3 : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
  have h3' : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hexp : (7:ℝ) = (r:ℝ)^2 + 3*(s:ℝ)^2 + 2*(r:ℝ)*(s:ℝ)*Real.sqrt 3 := by
    rw [← Real.sq_sqrt (show (0:ℝ) ≤ 7 by norm_num), h]
    ring_nf
    rw [h3']
  by_cases hs : s = 0
  · rw [hs] at h
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact irrational_sqrt7.ne_rat r h
  · by_cases hr : r = 0
    · have hs2 : (s:ℝ)^2 = 7/3 := by
        have h' := hexp
        rw [hr] at h'
        ring_nf at h'
        linarith
      have h21eq : Real.sqrt 21 = |(3:ℝ)*(s:ℝ)| := by
        rw [← Real.sqrt_sq_eq_abs]
        congr 1
        rw [mul_pow]
        norm_num
        linarith
      refine irrational_sqrt21.ne_rat (|3*s|) ?_
      rw [Rat.cast_abs]
      push_cast
      exact h21eq
    · have hsR : (s:ℝ) ≠ 0 := by exact_mod_cast hs
      have hrR : (r:ℝ) ≠ 0 := by exact_mod_cast hr
      have hsqrt : Real.sqrt 3 = (7 - (r:ℝ)^2 - 3*(s:ℝ)^2) / (2*(r:ℝ)*(s:ℝ)) := by
        field_simp
        linarith
      have hrat : (7 - (r:ℝ)^2 - 3*(s:ℝ)^2) / (2*(r:ℝ)*(s:ℝ)) =
          (((7 - r^2 - 3*s^2) / (2*r*s) : ℚ) : ℝ) := by
        push_cast
        ring
      exact hirr3.ne_rat ((7 - r^2 - 3*s^2) / (2*r*s)) (by rw [← hrat]; exact hsqrt)

end Freiman

open Freiman

-- Freiman.lowerHistory_inv_value: the certificate-field inversion is the real inverse.
theorem solution (z : CertField) (hz : certFieldVal z ≠ 0) :
    certFieldVal (lowerHistoryInv z) = (certFieldVal z)⁻¹ := by
  rw [lowerHistoryInv]
  set u : ℚ := z.a^2 + 3*z.b^2 - 7*z.c^2 - 21*z.d^2 with hu
  set v : ℚ := 2*z.a*z.b - 14*z.c*z.d with hv
  have h3' : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h7' : (Real.sqrt 7)^2 = 7 := Real.sq_sqrt (by norm_num)
  have h21 : Real.sqrt 21 = Real.sqrt 3 * Real.sqrt 7 := by
    rw [show (21:ℝ) = 3*7 by norm_num, Real.sqrt_mul (by norm_num)]
  have hAB : certFieldVal z * certFieldVal (⟨z.a, z.b, -z.c, -z.d⟩ : CertField)
      = (u:ℝ) + (v:ℝ)*Real.sqrt 3 := by
    rw [← certFieldVal_mul']
    simp only [certFieldMul, certFieldVal, h21]
    rw [hu, hv]
    push_cast
    ring_nf
  have hB : certFieldVal (⟨z.a, z.b, -z.c, -z.d⟩ : CertField)
      = ((u:ℝ) + (v:ℝ)*Real.sqrt 3) / certFieldVal z := by
    rw [eq_div_iff hz, mul_comm]
    exact hAB
  have hval2 : certFieldVal (⟨u, -v, 0, 0⟩ : CertField) = (u:ℝ) - (v:ℝ)*Real.sqrt 3 := by
    simp only [certFieldVal]; push_cast; ring
  have key : u = 0 → v = 0 → certFieldVal z = 0 := by
    intro hu0 hv0
    have hP0 : (z.a:ℝ)^2 + 3*(z.b:ℝ)^2 - 7*(z.c:ℝ)^2 - 21*(z.d:ℝ)^2 = 0 := by
      have h := congrArg (fun q : ℚ => (q:ℝ)) hu0
      rw [hu] at h
      push_cast at h
      simpa using h
    have hQ0 : 2*(z.a:ℝ)*(z.b:ℝ) - 14*(z.c:ℝ)*(z.d:ℝ) = 0 := by
      have h := congrArg (fun q : ℚ => (q:ℝ)) hv0
      rw [hv] at h
      push_cast at h
      simpa using h
    have h1 : (z.a:ℝ)^2 + 3*(z.b:ℝ)^2 = 7*(z.c:ℝ)^2 + 21*(z.d:ℝ)^2 := by linarith
    have h2 : 2*(z.a:ℝ)*(z.b:ℝ) = 14*(z.c:ℝ)*(z.d:ℝ) := by linarith
    have hPQ : ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3)^2
        = 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3)^2 := by
      have e1 : ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3)^2
          = (z.a:ℝ)^2 + 3*(z.b:ℝ)^2 + 2*(z.a:ℝ)*(z.b:ℝ)*Real.sqrt 3 := by
        ring_nf; rw [h3']
      have e2 : 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3)^2
          = 7*((z.c:ℝ)^2 + 3*(z.d:ℝ)^2 + 2*(z.c:ℝ)*(z.d:ℝ)*Real.sqrt 3) := by
        ring_nf; rw [h3']; ring
      rw [e1, e2]
      linear_combination h1 + Real.sqrt 3 * h2
    have hfac : ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3 - Real.sqrt 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3))
        * ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3 + Real.sqrt 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3)) = 0 := by
      have hf : ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3 - Real.sqrt 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3))
          * ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3 + Real.sqrt 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3))
          = ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3)^2 - 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3)^2 := by
        ring_nf
        rw [h7']
        ring
      rw [hf, hPQ, sub_self]
    rcases mul_eq_zero.mp hfac with hcase | hcase
    · have hP' : (z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3
          = Real.sqrt 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3) := by linarith
      by_cases hQnz : (z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3 = 0
      · have hP0' : (z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3 = 0 := by rw [hP', hQnz, mul_zero]
        have hval : certFieldVal z
            = ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3)
              + Real.sqrt 7 * ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3) := by
          simp only [certFieldVal, h21]; ring
        rw [hval, hP0', hQnz, mul_zero, add_zero]
      · have hQQ : ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3) * ((z.c:ℝ) - (z.d:ℝ)*Real.sqrt 3)
            = ((z.c:ℝ)^2 - 3*(z.d:ℝ)^2) := by
          ring_nf; rw [h3']
        have hN : ((z.c:ℝ)^2 - 3*(z.d:ℝ)^2) ≠ 0 := by
          intro h0
          have hprod : ((z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3) * ((z.c:ℝ) - (z.d:ℝ)*Real.sqrt 3) = 0 := by
            rw [hQQ, h0]
          rcases mul_eq_zero.mp hprod with h1' | h2'
          · exact hQnz h1'
          · have h2'' : (z.c:ℝ) + ((-z.d : ℚ):ℝ) * Real.sqrt 3 = 0 := by
              rw [Rat.cast_neg]; linarith
            have hcd := rat_add_rat_mul_sqrt3_eq_zero z.c (-z.d) h2''
            have hzq : (z.c:ℝ) + (z.d:ℝ)*Real.sqrt 3 = 0 := by
              have hd : z.d = 0 := neg_eq_zero.mp hcd.2
              rw [hcd.1, hd]; ring
            exact hQnz hzq
        have hPQbar : ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3) * ((z.c:ℝ) - (z.d:ℝ)*Real.sqrt 3)
            = Real.sqrt 7 * ((z.c:ℝ)^2 - 3*(z.d:ℝ)^2) := by
          rw [hP', mul_assoc, hQQ]
        have hL : ((z.a:ℝ) + (z.b:ℝ)*Real.sqrt 3) * ((z.c:ℝ) - (z.d:ℝ)*Real.sqrt 3)
            = ((z.a:ℝ)*(z.c:ℝ) - 3*(z.b:ℝ)*(z.d:ℝ))
              + ((z.b:ℝ)*(z.c:ℝ) - (z.a:ℝ)*(z.d:ℝ)) * Real.sqrt 3 := by
          ring_nf; rw [h3']; ring
        have hkey : Real.sqrt 7 = (((z.a*z.c - 3*z.b*z.d) / (z.c^2-3*z.d^2) : ℚ) : ℝ)
            + (((z.b*z.c - z.a*z.d) / (z.c^2-3*z.d^2) : ℚ) : ℝ) * Real.sqrt 3 := by
          have hrhs : (((z.a*z.c - 3*z.b*z.d) / (z.c^2-3*z.d^2) : ℚ) : ℝ)
              + (((z.b*z.c - z.a*z.d) / (z.c^2-3*z.d^2) : ℚ) : ℝ) * Real.sqrt 3
              = (((z.a:ℝ)*(z.c:ℝ) - 3*(z.b:ℝ)*(z.d:ℝ))
                + ((z.b:ℝ)*(z.c:ℝ) - (z.a:ℝ)*(z.d:ℝ)) * Real.sqrt 3)
                / ((z.c:ℝ)^2 - 3*(z.d:ℝ)^2) := by
            push_cast
            field_simp
          rw [hrhs, eq_div_iff hN]
          rw [← hL, hPQbar]
        exfalso
        exact sqrt7_ne_rat_add_rat_mul_sqrt3 ((z.a*z.c - 3*z.b*z.d)/(z.c^2-3*z.d^2))
          ((z.b*z.c - z.a*z.d)/(z.c^2-3*z.d^2)) hkey
    · simp only [certFieldVal, h21]
      linarith
  have hden : (u:ℝ)^2 - 3*(v:ℝ)^2 ≠ 0 := by
    intro hzero
    have hfac : ((u:ℝ) + (v:ℝ)*Real.sqrt 3) * ((u:ℝ) - (v:ℝ)*Real.sqrt 3) = 0 := by
      have hf : ((u:ℝ) + (v:ℝ)*Real.sqrt 3) * ((u:ℝ) - (v:ℝ)*Real.sqrt 3)
          = (u:ℝ)^2 - 3*(v:ℝ)^2 := by
        ring_nf; rw [h3']
      rw [hf, hzero]
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have h' := rat_add_rat_mul_sqrt3_eq_zero u v h1
      exact hz (key h'.1 h'.2)
    · have h2' : (u:ℝ) + ((-v : ℚ):ℝ) * Real.sqrt 3 = 0 := by push_cast; linarith
      have h' := rat_add_rat_mul_sqrt3_eq_zero u (-v) h2'
      exact hz (key h'.1 (neg_eq_zero.mp h'.2))
  rw [certFieldVal_scale', certFieldVal_mul', hval2, hB]
  push_cast
  field_simp
  ring_nf
  rw [h3']
