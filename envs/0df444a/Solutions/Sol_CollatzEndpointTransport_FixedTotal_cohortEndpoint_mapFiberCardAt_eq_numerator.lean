-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortEndpoint_mapFiberCardAt_eq_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:28.307669+00:00
-- url     : https://prove2.me/submissions/ebb1567f-73f2-4d49-9e37-a47afff4e6cf

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_mapFiber_eq_numerator

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} (u : Fin M)
    {c : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s) :
    mapFiberCardAt (fixedSet (M - (u : ℕ)) s)
        (cohortEndpoint u) c =
      mapFiberCardAt (fixedSet (M - (u : ℕ)) s)
        (cohortNumeratorResidue (s := s)) c := by
  exact congrArg Finset.card (cohortEndpoint_mapFiber_eq_numerator u hc)
end CollatzEndpointTransport.FixedTotal
