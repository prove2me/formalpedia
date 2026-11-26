-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSizeReverseRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:51:07.686452+00:00
-- url     : https://prove2.me/submissions/06e8d85d-1cbf-4247-868e-954ad2f8ca65

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_three_rpow


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} (htheta : 0 < theta) (hpi : 0 ≤ pi) :
    0 ≤ fixedSizeReverseRatio theta pi := by
  unfold fixedSizeReverseRatio
  have hthree : 0 ≤ (3 : ℝ) ^ theta - 1 := by
    linarith [one_lt_three_rpow htheta]
  exact div_nonneg (by positivity) (by positivity)
end CollatzEndpointTransport.FixedTotal
