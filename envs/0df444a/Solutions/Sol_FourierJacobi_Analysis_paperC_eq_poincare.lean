-- Prove2me | solution 1 for FourierJacobi.Analysis.paperC_eq_poincare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:19.514989+00:00
-- url     : https://prove2.me/submissions/4082e961-e11e-465a-88d5-8fcd3dce1d2a

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_coe_sq

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 ≤ q) :
    paperC q = poincare (inverseSqrt q : ℂ) := by
  have h := inverseSqrt_coe_sq q hq
  unfold paperC poincare
  rw [← h]
  ring
end FourierJacobi.Analysis
