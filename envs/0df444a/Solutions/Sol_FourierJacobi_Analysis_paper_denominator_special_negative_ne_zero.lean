-- Prove2me | solution 1 for FourierJacobi.Analysis.paper_denominator_special_negative_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:17.412291+00:00
-- url     : https://prove2.me/submissions/c88bd177-db3a-4266-b8b6-1c8a6fba3d34

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Analysis_paperC_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_paperD1_ne_zero_of_norm_le_one
import Theorems.Thm_FourierJacobi_Analysis_paperD2_special_negative
import Theorems.Thm_FourierJacobi_Algebra_coe_norm_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Algebra_satakeNumerator_unitary_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ -1) (hb₁ : b ≠ -1) :
    paperC q * paperD1 q a b (-(inverseSqrt q : ℂ)) *
      paperD2 q a b (-(inverseSqrt q : ℂ)) ≠ 0 := by
  have htn : ‖-(inverseSqrt q : ℂ)‖ ≤ 1 := by
    simpa only [norm_neg] using
      (coe_norm_lt_one (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)).le
  apply mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b _ ha hb htn))
  rw [paperD2_special_negative q hq a b ha hb]
  apply satakeNumerator_unitary_ne_zero ha hb
  · intro he
    apply ha₁
    linear_combination he
  · intro he
    apply hb₁
    linear_combination he
end FourierJacobi.Analysis
