-- Prove2me | solution 1 for FourierJacobi.Analysis.paperD1_ne_zero_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:13.072539+00:00
-- url     : https://prove2.me/submissions/d31742b6-8c17-48f1-b2ed-e3b33f447fd9

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_P2M_FourierJacobi_Analysis_paperD1_eq_d__2c658d5c8fde
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ ≤ 1) :
    paperD1 q a b d ≠ 0 := by
  rw [paperD1_eq_d₁]
  apply fourFactors_ne_zero ha hb
  have ht₀ := inverseSqrt_pos hq
  have ht₁ := inverseSqrt_lt_one hq
  have htn : ‖(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht₀]
  rw [norm_mul, htn]
  nlinarith
end FourierJacobi.Analysis
