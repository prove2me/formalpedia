-- Prove2me | solution 1 for FourierJacobi.Analysis.paper_denominator_special_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:01.977926+00:00
-- url     : https://prove2.me/submissions/c1d2a6da-45a0-4b8e-b32d-974ff61363a8

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Analysis_paper_denominator_special_positive_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_paper_denominator_special_negative_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b ε : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hε : ε = 1 ∨ ε = -1) (haε : a ≠ ε) (hbε : b ≠ ε) :
    paperC q * paperD1 q a b (ε * (inverseSqrt q : ℂ)) *
      paperD2 q a b (ε * (inverseSqrt q : ℂ)) ≠ 0 := by
  rcases hε with rfl | rfl
  · simpa only [one_mul] using
      paper_denominator_special_positive_ne_zero q hq a b ha hb haε hbε
  · simpa only [neg_one_mul] using
      paper_denominator_special_negative_ne_zero q hq a b ha hb haε hbε
end FourierJacobi.Analysis
