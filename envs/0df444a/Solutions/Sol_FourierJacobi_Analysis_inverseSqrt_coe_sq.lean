-- Prove2me | solution 1 for FourierJacobi.Analysis.inverseSqrt_coe_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:21.335826+00:00
-- url     : https://prove2.me/submissions/bcf389cb-0c37-4ab8-b491-3aed24b118f7

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_sq


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 ≤ q) :
    (inverseSqrt q : ℂ) ^ 2 = (q : ℂ)⁻¹ := by
  exact_mod_cast inverseSqrt_sq hq
end FourierJacobi.Analysis
