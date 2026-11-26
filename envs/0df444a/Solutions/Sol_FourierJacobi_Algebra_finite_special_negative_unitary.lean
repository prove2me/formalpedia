-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_special_negative_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:59.379985+00:00
-- url     : https://prove2.me/submissions/b64c6849-2369-4087-94c2-4c5b4c45d319

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_poincare_coe_ne_zero
import Theorems.Thm_P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320
import Theorems.Thm_FourierJacobi_Algebra_satakeNumerator_unitary_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_finiteRegular_special_negative
import Theorems.Thm_FourierJacobi_Algebra_finite_sum_special_negative_formula
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_one_sub_mul_ne_zero_of_norm_lt_one


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution (q t : ℝ) (a b : ℂ)
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (t : ℂ) a b (-(t : ℂ))) *
      specialNormalizer (t : ℂ) a b (-1) = 2 / ((q : ℂ) + 1) := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht₀
  have hx₂ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hx₄ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (4 : ℕ) ≠ 0)
  apply finite_sum_special_negative_formula (q : ℂ) (t : ℂ) a b
    (finiteRegular_special_negative ht₀ ht₁ ha hb ha₁ hb₁ hab hab₁ hA hB)
    htne (poincare_coe_ne_zero t) (satakeNumerator_unitary_ne_zero ha hb hA hB)
    (fourFactors_ne_zero ha hb hx₂) (n₂_unitary_ne_zero (le_of_lt ht₀) ht₁ ha hb)
    (fourFactors_ne_zero ha hb (by simpa using hx₂))
  · simpa using one_sub_mul_ne_zero_of_norm_lt_one (norm_one : ‖(1 : ℂ)‖ = 1) hx₂
  · simpa using one_sub_mul_ne_zero_of_norm_lt_one (norm_one : ‖(1 : ℂ)‖ = 1) hx₄
end FourierJacobi.Algebra
