-- Prove2me | solution 1 for FD1D.MonotoneQuantilePolicy.quantileDistance_eq_cdfTransportArea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:13.499479+00:00
-- url     : https://prove2.me/submissions/51bf517b-cec3-43a8-8cf2-ac67168e9fa6

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.MonotoneQuantilePolicy
namespace FD1D.MonotoneQuantilePolicy
theorem _root_.solution {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    P.quantileDistance = cdfTransportArea (fun z => F z - z) := by
  exact integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
    P.cdf_measurable P.quantile_measurable P.cdf_mapsTo P.quantile_mapsTo
    P.generalizedInverse
end FD1D.MonotoneQuantilePolicy
