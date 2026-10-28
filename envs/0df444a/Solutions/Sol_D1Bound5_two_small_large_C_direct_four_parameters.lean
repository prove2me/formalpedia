-- Prove2me | solution 1 for D1Bound5.two_small_large_C_direct_four_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:41.255509+00:00
-- url     : https://prove2.me/submissions/099c3b0c-70a1-4c5f-a0af-2fb1c4113c28

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5



theorem _root_.solution
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hT : 0 < T) (hS8 : S < (10 : ℝ)^8) (hT8 : T < (10 : ℝ)^8)
    (hC : (10 : ℝ)^100 ≤ C) (hV : (2/5 : ℝ)*A^2*C^5/T^2 < D) :
    1000*C ≤ D ∧ 17*A*B*S*T*C^3 ≤ D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hA2 : 1 ≤ A^2 := by nlinarith only [hA,sq_nonneg (A-1)]
  have hC0 : 0 < C := by norm_num at hC; linarith only [hC]
  have hT2 : T^2 < ((10 : ℝ)^8)^2 := by gcongr
  have hC2 : (10 : ℝ)^200 ≤ C^2 := by
    have hh : ((10 : ℝ)^100)^2 ≤ C^2 := by gcongr
    norm_num at hh ⊢
    exact hh
  have hD5 : C^5/(3*(10 : ℝ)^16) < D := by
    apply lt_trans _ hV
    apply (div_lt_div_iff₀ (by positivity) (sq_pos_of_pos hT)).2
    have hh := mul_lt_mul_of_pos_left hT2 (by positivity : 0 < C^5)
    have hh' := mul_le_mul_of_nonneg_right hA2 (by positivity : 0 ≤ C^5)
    norm_num at hh
    nlinarith only [hh,hh',pow_pos hC0 5]
  have hbig : (10 : ℝ)^20*C^3 < D := by
    apply lt_trans _ hD5
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3*10^16)).2
    have hh := mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ C^3)
    norm_num at hh ⊢
    nlinarith only [hh,pow_pos hC0 3]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hC2 hC0.le
    norm_num at hh hbig
    nlinarith only [hh,hbig,hC0]
  · have hprod : A*B*S*T < 9*((10 : ℝ)^8)^2 := by
      calc
        _ ≤ B*B*S*T := by gcongr
        _ < 3*3*((10 : ℝ)^8)*((10 : ℝ)^8) := by gcongr
        _ = _ := by ring
    have hh := mul_lt_mul_of_pos_right hprod (by positivity : 0 < C^3)
    norm_num at hh hbig
    nlinarith only [hh,hbig,pow_pos hC0 3]



end D1Bound5
end
