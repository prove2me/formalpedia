-- Prove2me | solution 1 for FourierJacobi.Algebra.fourFactors_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:05.368461+00:00
-- url     : https://prove2.me/submissions/72a1adc0-7202-41f8-ac2d-ca41e7db1bc4

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Theorems.Thm_FourierJacobi_Algebra_one_sub_mul_ne_zero_of_norm_lt_one

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {a b x : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) :
    fourFactors a b x ≠ 0 := by
  have hai : ‖a⁻¹‖ = 1 := by simp [ha]
  have hbi : ‖b⁻¹‖ = 1 := by simp [hb]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (one_sub_mul_ne_zero_of_norm_lt_one ha hx)
    (one_sub_mul_ne_zero_of_norm_lt_one hai hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hb hx))
    (one_sub_mul_ne_zero_of_norm_lt_one hbi hx)
end FourierJacobi.Algebra
