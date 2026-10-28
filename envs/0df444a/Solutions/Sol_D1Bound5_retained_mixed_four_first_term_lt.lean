-- Prove2me | solution 1 for D1Bound5.retained_mixed_four_first_term_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:22.98303+00:00
-- url     : https://prove2.me/submissions/b6e14868-7f86-4d63-bdb4-4b1a8dd9ee8c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- With A≥1 and B≥3, the first summand of the actual four-anchor form is below one percent
after the retained five-entry growth has been established. -/
theorem _root_.solution
    (A B S T C D Z : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B)
    (hS : 0 < S) (hT : 0 < T) (hZ : 0 < Z)
    (hC : 16*B*S*T < C)
    (hD : A^2*C^5/S^2 < D)
    (hroot : (3999/4000 : ℝ)*C*D < Z^2) :
    13*B*S^2*T^3/Z < (1/100 : ℝ) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hC0 : 0 < C := (by positivity : 0 < 16*B*S*T).trans hC
  have hC6 : (16*B*S*T)^6 < C^6 := by
    gcongr
  have hD' := (div_lt_iff₀ (pow_pos hS 2)).mp hD
  have hD'' := mul_lt_mul_of_pos_left hD'
    (by positivity : 0 < (3999/4000 : ℝ)*C)
  have hroot' := mul_lt_mul_of_pos_right hroot (pow_pos hS 2)
  have hC6' := mul_lt_mul_of_pos_left hC6
    (by positivity : 0 < (3999/4000 : ℝ)*A^2)
  have hbig : (3999/4000 : ℝ)*A^2*(16*B*S*T)^6 < Z^2*S^2 := by
    nlinarith only [hC6', hD'', hroot']
  have hAB : (81 : ℝ) ≤ A^2*B^4 := by
    calc
      (81 : ℝ) = 1^2*3^4 := by norm_num
      _ ≤ A^2*B^4 := by gcongr
  have hcoef : (10000*169 : ℝ) < (3999/4000 : ℝ)*16^6*(A^2*B^4) := by
    nlinarith only [hAB]
  have hcoef' := mul_lt_mul_of_pos_right hcoef
    (by positivity : 0 < B^2*S^6*T^6)
  have hsquare : (100*(13*B*S^2*T^3))^2 < Z^2 := by
    apply (mul_lt_mul_iff_of_pos_right (pow_pos hS 2)).mp
    nlinarith only [hcoef', hbig]
  have hlinear : 100*(13*B*S^2*T^3) < Z := by
    by_contra h
    have hh : Z ≤ 100*(13*B*S^2*T^3) := le_of_not_gt h
    have hp := mul_nonneg (sub_nonneg.mpr hh)
      (by positivity : 0 ≤ 100*(13*B*S^2*T^3)+Z)
    nlinarith only [hp, hsquare]
  apply (div_lt_iff₀ hZ).2
  nlinarith only [hlinear]



end D1Bound5
end
