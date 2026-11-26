-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumerator_injOn_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:29:03.888904+00:00
-- url     : https://prove2.me/submissions/ee366976-42c3-42f9-93e6-9cbf769f8d37

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injective_on_length


set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) :
    Set.InjOn syracuseNumerator (↑(fixedSet N s) : Set (Composition N)) := by
  intro c hc d hd hnum
  exact syracuseNumerator_injective_on_length
    (Finset.mem_filter.mp hc).2
    (Finset.mem_filter.mp hd).2
    hnum
end CollatzEndpointTransport.FixedTotal
