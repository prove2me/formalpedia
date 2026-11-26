-- Prove2me | solution 1 for FourierJacobi.Algebra.finiteRegular_special_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:28.529956+00:00
-- url     : https://prove2.me/submissions/b2a00462-d152-449e-91f2-b59ceb6fb98f

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_weylU_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_unitary
import Theorems.Thm_FourierJacobi_Algebra_weylV_one_add_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_satakeNumerator_unitary_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_regionRegular_special_negative
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_weyl_common_euler_factorization
import Theorems.Thm_P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe
import Theorems.Thm_P2M_FourierJacobi_Algebra_special_negative_d__a6d88199088c


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {a b : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) :
    FiniteRegular (t : ℂ) a b (-(t : ℂ)) := by
  have ha₀ := unit_ne_zero ha
  have hb₀ := unit_ne_zero hb
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht₀
  have hd₀ : -(t : ℂ) ≠ 0 := neg_ne_zero.mpr htne
  have hx₂ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (2 : ℕ) ≠ 0)
  have hf : fourFactors a b (-(t : ℂ) ^ 2) ≠ 0 :=
    fourFactors_ne_zero ha hb (by simpa using hx₂)
  have hD₁ : d₁ (t : ℂ) a b (-(t : ℂ)) ≠ 0 := by
    rwa [special_negative_d₁]
  have hD₂ : d₂ (t : ℂ) a b (-(t : ℂ)) ≠ 0 := by
    rw [special_negative_d₂ (t : ℂ) a b htne ha₀ hb₀]
    exact satakeNumerator_unitary_ne_zero ha hb hA hB
  have hWall : weylWall a b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha₁ hab) hb₁) hab₁
  refine ⟨ha₀, hb₀, hd₀, ha₁, hb₁, hab, hab₁, ?_, ?_⟩
  · rw [weyl_common_euler_factorization (t : ℂ) a b (-(t : ℂ)) ha₀ hb₀ hd₀]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hWall
        (pow_ne_zero 2 ha₀)) (pow_ne_zero 2 hb₀)) hd₀)
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) (pow_ne_zero 2 hb₀))
          (pow_ne_zero 4 hd₀)))
      (mul_ne_zero hD₁ hD₂)
  · intro i
    exact regionRegular_special_negative ht₀ ht₁ (weylU_unitary ha hb i)
      (weylV_unitary ha hb i) (weylV_one_add_ne_zero ha₀ hb₀ hA hB i)
end FourierJacobi.Algebra
