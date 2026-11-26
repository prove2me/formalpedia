-- Prove2me | solution 1 for FourierJacobi.Algebra.principal_final_denominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:40.990787+00:00
-- url     : https://prove2.me/submissions/2d8d7e00-f835-4819-bfd1-28a212fda892

import Definitions.Def_FourierJacobi_Algebra_EulerFactors
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Theorems.Thm_FourierJacobi_Algebra_one_add_mul_ne_zero_of_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {t : ℝ} {d : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hd : ‖d‖ = 1) :
    (1 + d * (t : ℂ)) * (1 + (t : ℂ) / d) ≠ 0 := by
  have hx := coe_norm_lt_one ht₀ ht₁
  have hi : ‖d⁻¹‖ = 1 := by simp [hd]
  exact mul_ne_zero (one_add_mul_ne_zero_of_norm_lt_one hd hx)
    (by simpa [div_eq_mul_inv, mul_comm] using
      one_add_mul_ne_zero_of_norm_lt_one hi hx)
end FourierJacobi.Algebra
