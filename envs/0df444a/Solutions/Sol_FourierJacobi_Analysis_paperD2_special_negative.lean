-- Prove2me | solution 1 for FourierJacobi.Analysis.paperD2_special_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:38:26.707801+00:00
-- url     : https://prove2.me/submissions/58c59289-11b8-4ea5-b76a-5d1331a56c94

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero
import Theorems.Thm_P2M_FourierJacobi_Algebra_special_negative_d__a6d88199088c


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    paperD2 q a b (-(inverseSqrt q : ℂ)) = satakeNumerator a b := by
  rw [paperD2_eq_d₂]
  have htne : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  exact special_negative_d₂ _ _ _ htne (unit_ne_zero ha) (unit_ne_zero hb)
end FourierJacobi.Analysis
