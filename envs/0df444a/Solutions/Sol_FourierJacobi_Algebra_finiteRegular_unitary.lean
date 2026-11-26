-- Prove2me | solution 1 for FourierJacobi.Algebra.finiteRegular_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:40.617882+00:00
-- url     : https://prove2.me/submissions/e747f834-13da-4e50-8b7f-cbc472fcdbe8

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_unitary
import Theorems.Thm_FourierJacobi_Algebra_regionRegular_unitary
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_weyl_common_euler_factorization


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {a b d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) : FiniteRegular (t : ℂ) a b d := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  have hd₀ := unit_ne_zero hd
  have hx := coe_norm_lt_one ht₀ ht₁
  have hdt : ‖d * (t : ℂ)‖ < 1 := by simpa [norm_mul, hd] using hx
  have htd : ‖(t : ℂ) / d‖ < 1 := by simpa [norm_div, hd] using hx
  have hD₁ : d₁ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb hdt
  have hD₂ : d₂ (t : ℂ) a b d ≠ 0 := fourFactors_ne_zero ha hb htd
  have hWall : weylWall a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha₁ hab) hb₁) hab₁
  refine ⟨ha₀, hb₀, hd₀, ha₁, hb₁, hab, hab₁, ?_, ?_⟩
  · rw [weyl_common_euler_factorization (t : ℂ) a b d ha₀ hb₀ hd₀]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hWall
        (pow_ne_zero 2 ha₀)) (pow_ne_zero 2 hb₀)) hd₀)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) (pow_ne_zero 2 hb₀))
          (pow_ne_zero 4 hd₀)))
      (mul_ne_zero hD₁ hD₂)
  · intro i
    exact regionRegular_unitary ht₀ ht₁ hd (weylU_unitary ha hb i) (weylV_unitary ha hb i)
end FourierJacobi.Algebra
