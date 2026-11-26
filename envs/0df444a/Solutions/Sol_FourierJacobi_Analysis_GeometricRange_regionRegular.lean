-- Prove2me | solution 1 for FourierJacobi.Analysis.GeometricRange.regionRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:52.543666+00:00
-- url     : https://prove2.me/submissions/939e3c3f-bc70-4816-9b98-fa05ffa6de37

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Theorems.Thm_FourierJacobi_Analysis_norm_one_sub_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
namespace GeometricRange
theorem _root_.solution {t d U V T : ℂ}
    (h : GeometricRange t d U V T) : RegionRegular t d (T * U) (T * V) := by
  refine ⟨?_, norm_one_sub_ne_zero h.n, norm_one_sub_ne_zero h.e,
    norm_one_sub_ne_zero h.f, norm_one_sub_ne_zero h.g⟩
  apply norm_one_sub_ne_zero
  simpa only [mul_assoc] using h.p
end GeometricRange
end FourierJacobi.Analysis
