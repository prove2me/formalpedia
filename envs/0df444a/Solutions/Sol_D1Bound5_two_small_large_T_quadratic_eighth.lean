-- Prove2me | solution 1 for D1Bound5.two_small_large_T_quadratic_eighth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:24.216742+00:00
-- url     : https://prove2.me/submissions/d7e53edb-c1a2-40e3-ba4e-c1b3c47a79db

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5





theorem _root_.solution
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hS : 3 ≤ S) (hT : 0 < T)
    (hC : 5*A*B*S*T^2 < C) (hV : (2/5 : ℝ)*A^2*C^5/T^2 < D) :
    T^8 < D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS]
  have hAB : 1 ≤ A*B := by
    have hh := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1) hA0.le
    simpa only [one_mul] using hh
  have hCsmall : 5*S*T^2 < C := by
    have hh := mul_le_mul_of_nonneg_right hAB (by positivity : 0 ≤ 5*S*T^2)
    nlinarith only [hh,hC]
  have hC0 : 0 < C := (by positivity : 0 < 5*S*T^2).trans hCsmall
  have hc5 : (5*S*T^2)^5 < C^5 := by gcongr
  have hA2 : (1 : ℝ) ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
  have hscaled := mul_le_mul_of_nonneg_right hA2 (by positivity : 0 ≤ C^5)
  have hs5 : (3 : ℝ)^5 ≤ S^5 := by gcongr
  have hsprod := mul_le_mul_of_nonneg_right hs5 (by positivity : 0 ≤ T^10)
  have hcompare : T^8 < (2/5 : ℝ)*A^2*C^5/T^2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hT)).2
    nlinarith only [hc5,hscaled,hsprod,pow_pos hT 10]
  exact hcompare.trans hV



end D1Bound5
end
