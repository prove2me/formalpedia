-- Prove2me | solution 1 for FourierJacobi.Algebra.finite_principal_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:10.741829+00:00
-- url     : https://prove2.me/submissions/3c72a11c-3850-44b3-9755-7a0422046018

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_poincare_coe_ne_zero
import Theorems.Thm_P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320
import Theorems.Thm_FourierJacobi_Algebra_finiteRegular_unitary
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_finite_sum_principal_formula
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_one_add_mul_ne_zero_of_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_one_sub_mul_ne_zero_of_norm_lt_one


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution (q t : ℝ) (a b d : ℂ)
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) :
    (2 / ((q : ℂ) + 1) * finiteCore (t : ℂ) a b d) *
      principalNormalizer (t : ℂ) a b d =
      2 / ((q : ℂ) + 1) * (a + 2 + a⁻¹) * (b + 2 + b⁻¹) /
        ((1 + d * (t : ℂ)) * (1 + (t : ℂ) / d)) := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hx₂ := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hdi : ‖d⁻¹‖ = 1 := by simp [hd]
  have hdt : ‖d * (t : ℂ)‖ < 1 := by simpa [norm_mul, hd] using hx
  have htd : ‖(t : ℂ) / d‖ < 1 := by simpa [norm_div, hd] using hx
  apply finite_sum_principal_formula (q : ℂ) (t : ℂ) a b d
    (finiteRegular_unitary ht₀ ht₁ ha hb hd ha₁ hb₁ hab hab₁)
    (poincare_coe_ne_zero t) (fourFactors_ne_zero ha hb hx₂)
    (n₂_unitary_ne_zero ht₀ ht₁ ha hb)
    (fourFactors_ne_zero ha hb hdt) (fourFactors_ne_zero ha hb htd)
  · simpa using one_sub_mul_ne_zero_of_norm_lt_one (norm_one : ‖(1 : ℂ)‖ = 1) hx₂
  · exact one_sub_mul_ne_zero_of_norm_lt_one hd hx
  · exact one_add_mul_ne_zero_of_norm_lt_one hd hx
  · simpa [div_eq_mul_inv, mul_comm] using one_sub_mul_ne_zero_of_norm_lt_one hdi hx
  · simpa [div_eq_mul_inv, mul_comm] using one_add_mul_ne_zero_of_norm_lt_one hdi hx
end FourierJacobi.Algebra
