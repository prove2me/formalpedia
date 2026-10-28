-- Prove2me | solution 1 for D1Bound5.two_small_large_T_quintic_eighth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:08.153785+00:00
-- url     : https://prove2.me/submissions/96de721d-f1e1-4cfa-8bb2-5e9716c3f33c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5







theorem _root_.solution
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hS : 0 < S)
    (hS8 : S < (10 : ℝ)^8) (hT : 0 < T)
    (hC : A^2*T^5/(37*S^2) < C) (hcross : A^3*B*T^3*C/(7*S) < D) :
    T^8/(10 : ℝ)^27 < D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hC0 : 0 < C := (by positivity : 0 < A^2*T^5/(37*S^2)).trans hC
  have hA2 : (1 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
  have hA3 : 1 ≤ A^3 := by calc
    1 = (1 : ℝ)^3 := by norm_num
    _ ≤ A^3 := by gcongr
  have hA3B : 1 ≤ A^3*B := by
    have hh := mul_le_mul hA3 hB (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ A^3)
    simpa only [one_mul] using hh
  have hCweak : T^5/(37*S^2) < C := by
    apply lt_of_le_of_lt _ hC
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hA2 (by positivity : 0 ≤ T^5)
    simpa only [one_mul] using hh
  have hcrossweak : T^3*C/(7*S) < D := by
    apply lt_of_le_of_lt _ hcross
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right hA3B (by positivity : 0 ≤ T^3*C)
    nlinarith only [hh]
  have hproduct : T^8/(259*S^3) < D := by
    calc
      _ = (T^3/(7*S))*(T^5/(37*S^2)) := by field_simp; ring
      _ < (T^3/(7*S))*C := mul_lt_mul_of_pos_left hCweak (by positivity)
      _ = T^3*C/(7*S) := by ring
      _ < D := hcrossweak
  have hS3 : S^3 < ((10 : ℝ)^8)^3 := by gcongr
  have hden : 259*S^3 < (10 : ℝ)^27 := by norm_num at hS3 ⊢; nlinarith only [hS3]
  exact (div_lt_div_of_pos_left (pow_pos hT 8) (by positivity : 0 < 259*S^3) hden).trans hproduct

end D1Bound5
end
