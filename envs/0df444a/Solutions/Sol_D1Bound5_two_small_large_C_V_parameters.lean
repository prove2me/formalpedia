-- Prove2me | solution 1 for D1Bound5.two_small_large_C_V_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:08.634333+00:00
-- url     : https://prove2.me/submissions/640b1032-a937-48c7-9ce3-21f3cc822052

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5

theorem _root_.solution
    (A B S T C D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hB3 : B < 3)
    (hS : 3 ≤ S) (hST : S ≤ T) (hS8 : S < (10 : ℝ)^8) (hT8 : T < (10 : ℝ)^8)
    (hC : (10 : ℝ)^100 ≤ C) (hD : 2*S*T*C < D) :
    1000 ≤ C ∧ 4*T ≤ C ∧ 4*C ≤ D ∧
      32*B*S*T/A^3 ≤ C^2 ∧ 101*B^2*T^4/C < D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS]
  have hT0 : 0 < T := hS0.trans_le hST
  have hC0 : 0 < C := by norm_num at hC; linarith only [hC]
  have hC2 : (10 : ℝ)^200 ≤ C^2 := by
    have hh : ((10 : ℝ)^100)^2 ≤ C^2 := by gcongr
    norm_num at hh ⊢
    exact hh
  have hST9 : 9 ≤ S*T := by
    have hh := mul_le_mul hS (hS.trans hST) (by norm_num) hS0.le
    norm_num at hh
    exact hh
  have hCD : 4*C ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hST9 hC0.le
    nlinarith only [hh,hD,hC0]
  have hsize : 32*B*S*T/A^3 ≤ C^2 := by
    have hprod : B*S*T < 3*((10 : ℝ)^8)^2 := by
      calc
        B*S*T < 3*(10 : ℝ)^8*(10 : ℝ)^8 := by gcongr
        _ = 3*((10 : ℝ)^8)^2 := by ring
    have hA3 : 1 ≤ A^3 := by calc
      1 = (1 : ℝ)^3 := by norm_num
      _ ≤ A^3 := by gcongr
    have hh := mul_le_mul_of_nonneg_right hA3 (sq_nonneg C)
    apply (div_le_iff₀ (by positivity : 0 < A^3)).2
    norm_num at hprod hC2
    nlinarith only [hh,hprod,hC2]
  have hwindow : 101*B^2*T^4/C < D := by
    have hprod : B^2*T^4 < (3 : ℝ)^2*((10 : ℝ)^8)^4 := by gcongr
    have hsmall : 101*B^2*T^4/C < 1 := by
      apply (div_lt_iff₀ hC0).2
      norm_num at hprod hC
      nlinarith only [hprod,hC]
    norm_num at hC
    linarith only [hsmall,hCD,hC]
  refine ⟨?_,?_,hCD,hsize,hwindow⟩
  · norm_num at hC; linarith only [hC]
  · norm_num at hC hT8; linarith only [hC,hT8]





end D1Bound5
end
