-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedCriticalNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:26:43.975608+00:00
-- url     : https://prove2.me/submissions/a35606a1-9307-438b-905e-57ca98e5bca6

import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment

set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.globalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) :
    0 ≤ fixedCriticalNumerator N s := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
end CollatzEndpointTransport.FixedTotal
