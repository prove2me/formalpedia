-- Prove2me | solution 1 for FourierJacobi.Analysis.inverseSqrt_coe_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:07.998228+00:00
-- url     : https://prove2.me/submissions/4df3d07c-462f-42cf-a184-9ce037d3dd49

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_coe_sq

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) :
    (q : ℂ) * (inverseSqrt q : ℂ) ^ 2 = 1 := by
  rw [inverseSqrt_coe_sq q (by linarith)]
  apply mul_inv_cancel₀
  exact_mod_cast (ne_of_gt (show 0 < q by linarith))
end FourierJacobi.Analysis
