-- Prove2me | solution 1 for D1Bound5.two_small_large_T_lower_window_impossible
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:59.783736+00:00
-- url     : https://prove2.me/submissions/e021696b-742d-4a31-970d-adc63c7a49e8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

section
namespace D1Bound5

theorem _root_.solution
    (B S T C : ℝ) (hB : 0 < B) (hB3 : B < 3) (hS : 0 < S)
    (hS8 : S < (10 : ℝ)^8) (hT : (10 : ℝ)^72 ≤ T) (hTC : T ≤ C) :
    ¬ C < 101*B^2*S^4/T := by
  have hB2 : B^2 < (3 : ℝ)^2 := by gcongr
  have hS4 : S^4 < ((10 : ℝ)^8)^4 := by gcongr
  have hnum : 101*B^2*S^4 < (10 : ℝ)^72 := by
    have hh := mul_lt_mul hB2 hS4.le (by positivity : 0 < S^4) (by norm_num : (0 : ℝ) ≤ 3^2)
    norm_num at hh ⊢
    nlinarith only [hh]
  have hT0 : 0 < T := by norm_num at hT; linarith only [hT]
  have hbound : 101*B^2*S^4/T < 1 := by
    apply (div_lt_iff₀ hT0).2
    simpa only [one_mul] using hnum.trans_le hT
  intro hbad
  norm_num at hT
  linarith only [hbad,hbound,hTC,hT]







end D1Bound5
end
