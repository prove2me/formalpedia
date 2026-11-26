-- Prove2me | solution 1 for FourierJacobi.Analysis.paperD2_ne_zero_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:38.519339+00:00
-- url     : https://prove2.me/submissions/7038ec5e-127a-48cb-93f3-6affbfe88337

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
import Theorems.Thm_FourierJacobi_Algebra_fourFactors_ne_zero
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd : inverseSqrt q < ‖d‖) : paperD2 q a b d ≠ 0 := by
  rw [paperD2_eq_d₂]
  apply fourFactors_ne_zero ha hb
  have ht₀ := inverseSqrt_pos hq
  have hd₀ : 0 < ‖d‖ := lt_trans ht₀ hd
  have htn : ‖(inverseSqrt q : ℂ)‖ = inverseSqrt q := by
    simp [abs_of_pos ht₀]
  rw [norm_div, htn]
  exact (div_lt_one hd₀).mpr hd
end FourierJacobi.Analysis
