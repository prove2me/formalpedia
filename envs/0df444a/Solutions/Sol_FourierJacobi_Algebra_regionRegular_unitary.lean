-- Prove2me | solution 1 for FourierJacobi.Algebra.regionRegular_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:21.166799+00:00
-- url     : https://prove2.me/submissions/7283e148-7834-4b34-a0d2-e6129777d6b2

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_one_sub_mul_ne_zero_of_norm_lt_one


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {d U V : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hd : ‖d‖ = 1)
    (hU : ‖U‖ = 1) (hV : ‖V‖ = 1) : RegionRegular (t : ℂ) d U V := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hx₂ := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hx₄ := coe_pow_norm_lt_one ht₀ ht₁ (by decide : (4 : ℕ) ≠ 0)
  have hdV : ‖d * V‖ = 1 := by simp [hd, hV]
  have hVd : ‖V / d‖ = 1 := by simp [hd, hV]
  have hV₂ : ‖V ^ 2‖ = 1 := by simp [hV]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact one_sub_mul_ne_zero_of_norm_lt_one hdV hx
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      one_sub_mul_ne_zero_of_norm_lt_one hVd hx
  · exact one_sub_mul_ne_zero_of_norm_lt_one hV₂ hx₂
  · exact one_sub_mul_ne_zero_of_norm_lt_one hU hx₂
  · exact one_sub_mul_ne_zero_of_norm_lt_one hU hx₄
end FourierJacobi.Algebra
