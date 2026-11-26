-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortCriticalNumerator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:55.506362+00:00
-- url     : https://prove2.me/submissions/25dc48de-49ec-40dd-9d3f-9bd955063c8b

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortCriticalNumerator_eq_fixed

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (u : Fin M) (s : ℕ) :
    cohortCriticalNumerator M u s ≤
      fixedCriticalNumerator (M - (u : ℕ)) s :=
  (cohortCriticalNumerator_eq_fixed M u s).le
end CollatzEndpointTransport.FixedTotal
