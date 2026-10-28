-- Prove2me | solution 1 for D1Bound5.two_small_large_C_seventh_power
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:18.878527+00:00
-- url     : https://prove2.me/submissions/6588d738-3dc5-4068-b9a1-1555facb1cb6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5





/-- The actual direct-four inequality forces seventh-power terminal
growth in the remaining small-anchor box. -/
theorem _root_.solution
    (A B S T C D Z : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hT : 0 < T) (hS8 : S < (10 : ℝ)^8) (hT8 : T < (10 : ℝ)^8)
    (hC : (10 : ℝ)^100 ≤ C) (hZ : 0 < Z) (hCZ : C/2 < Z)
    (hroot : Z^2 ≤ 2*C*D)
    (hform : 1 < 13*B*S^2*T^3/Z+49*S*T^2*Z/(50*A*C^4)) :
    C^7/(10 : ℝ)^50 < D := by
  have hA0 : 0 < A := by linarith only [hA]
  have hC0 : 0 < C := by norm_num at hC; linarith only [hC]
  have hfirst : 13*B*S^2*T^3/Z < (1/2 : ℝ) := by
    have hcoeff : B*S^2*T^3 < 3*((10 : ℝ)^8)^5 := by
      calc
        _ < 3*((10 : ℝ)^8)^2*((10 : ℝ)^8)^3 := by gcongr
        _ = _ := by ring
    apply (div_lt_iff₀ hZ).2
    norm_num at hcoeff hC
    nlinarith only [hcoeff,hCZ,hC]
  have hsecond : (1/2 : ℝ) < 49*S*T^2*Z/(50*A*C^4) := by
    linarith only [hform,hfirst]
  have hcoeff : S*T^2 < ((10 : ℝ)^8)^3 := by
    calc
      _ < ((10 : ℝ)^8)*((10 : ℝ)^8)^2 := by gcongr
      _ = _ := by ring
  have hclear := (lt_div_iff₀ (by positivity : 0 < 50*A*C^4)).1 hsecond
  have hcoefZ := mul_lt_mul_of_pos_right hcoeff hZ
  have hAclear := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ C^4)
  have hZlower : C^4 < 2*(10 : ℝ)^24*Z := by
    norm_num at hcoefZ
    nlinarith only [hclear,hcoefZ,hAclear,pow_pos hC0 4]
  have hsq : C^8 < 4*(10 : ℝ)^48*Z^2 := by
    have hh := mul_pos (sub_pos.mpr hZlower) (by positivity : 0 < 2*(10 : ℝ)^24*Z+C^4)
    norm_num at hh ⊢
    nlinarith only [hh]
  have hscaled := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ 4*10^48)
  have hD0 : 0 < D := by nlinarith only [hroot,sq_pos_of_pos hZ,hC0]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 10^50)).2
  apply (mul_lt_mul_iff_of_pos_left hC0).1
  norm_num at hsq hscaled ⊢
  nlinarith only [hsq,hscaled,mul_pos hC0 hD0]

end D1Bound5
end
