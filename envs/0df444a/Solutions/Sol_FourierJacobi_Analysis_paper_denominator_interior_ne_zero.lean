-- Prove2me | solution 1 for FourierJacobi.Analysis.paper_denominator_interior_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:59.543881+00:00
-- url     : https://prove2.me/submissions/2c4a536b-2386-40ee-acb3-04925b48ac18

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Analysis_paperC_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_paperD1_ne_zero_of_norm_le_one
import Theorems.Thm_FourierJacobi_Analysis_paperD2_ne_zero_interior

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : inverseSqrt q < ‖d‖) (hdhi : ‖d‖ ≤ 1) :
    paperC q * paperD1 q a b d * paperD2 q a b d ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero (paperC_ne_zero q hq)
      (paperD1_ne_zero_of_norm_le_one q hq a b d ha hb hdhi))
    (paperD2_ne_zero_interior q hq a b d ha hb hdlo)
end FourierJacobi.Analysis
