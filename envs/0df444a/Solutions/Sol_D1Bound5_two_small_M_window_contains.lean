-- Prove2me | solution 1 for D1Bound5.two_small_M_window_contains
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:27.422516+00:00
-- url     : https://prove2.me/submissions/8d751aa3-35a7-49ba-9deb-4af7ac81e29e

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5

/-- The actual M endpoints contain the simple power window throughout
the remaining two-small box. These are exact rational comparisons. -/
theorem _root_.solution
    (A B S C : ℝ) (hA : 1 ≤ A) (hB : 0 < B) (hB3 : B < 3)
    (hS : 0 < S) (hS8 : S < (10 : ℝ)^8) (hC : 0 < C) :
    4*((8/9 : ℝ)*608^2)^2*B^6*S^16*C^5/(1-1/4000 : ℝ) ≤ (10 : ℝ)^143*C^5 ∧
      C^11/(10 : ℝ)^87 ≤ A^6*C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) := by
  have hA0 : 0 < A := by linarith only [hA]
  constructor
  · have hb6 : B^6 < (3 : ℝ)^6 := by gcongr
    have hs16 : S^16 < ((10 : ℝ)^8)^16 := by gcongr
    have hh := mul_lt_mul hb6 hs16.le (by positivity : 0 < S^16) (by norm_num : (0 : ℝ) ≤ 3^6)
    have hcoef : 4*((8/9 : ℝ)*608^2)^2*B^6*S^16/(1-1/4000 : ℝ) ≤ (10 : ℝ)^143 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1-1/4000)).2
      norm_num at hh ⊢
      nlinarith only [hh]
    have hmul := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ C^5)
    simpa only [div_mul_eq_mul_div] using hmul
  · have hb4 : B^4 < (3 : ℝ)^4 := by gcongr
    have hs10 : S^10 < ((10 : ℝ)^8)^10 := by gcongr
    have hh := mul_lt_mul hb4 hs10.le (by positivity : 0 < S^10) (by norm_num : (0 : ℝ) ≤ 3^4)
    have hden : 4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ) < (10 : ℝ)^87 := by
      norm_num at hh ⊢
      nlinarith only [hh]
    have hA6 : 1 ≤ A^6 := by calc
      1 = (1 : ℝ)^6 := by norm_num
      _ ≤ A^6 := by gcongr
    calc
      C^11/(10 : ℝ)^87 ≤ C^11/(4*(3920/81 : ℝ)^2*B^4*S^10*(1+1/4000 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden.le
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hmul := mul_le_mul_of_nonneg_right hA6 (by positivity : 0 ≤ C^11)
        simpa only [one_mul] using hmul



end D1Bound5
end
