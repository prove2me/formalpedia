-- Prove2me | solution 1 for FourierJacobi.Analysis.paper_denominator_special_positive_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:58.535292+00:00
-- url     : https://prove2.me/submissions/ee66060e-6799-437b-b9d7-242af90ec959

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Analysis_paperC_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_paperD1_ne_zero_of_norm_le_one
import Theorems.Thm_FourierJacobi_Analysis_fourFactors_one_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_paperD2_special_positive
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) :
    paperC q * paperD1 q a b (inverseSqrt q : ℂ) *
      paperD2 q a b (inverseSqrt q : ℂ) ≠ 0 := by
  have htn : ‖(inverseSqrt q : ℂ)‖ ≤ 1 :=
    (coe_norm_lt_one (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)).le
  apply mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b _ ha hb htn))
  rw [paperD2_special_positive q hq]
  exact fourFactors_one_ne_zero a b ha₁ hb₁
end FourierJacobi.Analysis
