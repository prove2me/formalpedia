-- Prove2me | solution 1 for FourierJacobi.Algebra.regionRegular_special_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:04.278003+00:00
-- url     : https://prove2.me/submissions/866c1369-786c-4b01-b98d-2971104053d3

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_coe_pow_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_regionRegular_unitary
import Theorems.Thm_FourierJacobi_Algebra_one_add_mul_ne_zero_of_norm_lt_one


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {U V : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (hU : ‖U‖ = 1) (hV : ‖V‖ = 1)
    (hV₁ : 1 + V ≠ 0) : RegionRegular (t : ℂ) (-(t : ℂ)) U V := by
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht₀
  have hx₂ := coe_pow_norm_lt_one (le_of_lt ht₀) ht₁ (by decide : (2 : ℕ) ≠ 0)
  have base := regionRegular_unitary (le_of_lt ht₀) ht₁
    (norm_one : ‖(1 : ℂ)‖ = 1) hU hV
  refine ⟨?_, ?_, base.e, base.f, base.g⟩
  · convert one_add_mul_ne_zero_of_norm_lt_one hV hx₂ using 1
    ring
  · have he : V * (t : ℂ) / (-(t : ℂ)) = -V := by
      rw [div_neg, mul_div_cancel_right₀ V htne]
    simpa [he] using hV₁
end FourierJacobi.Algebra
