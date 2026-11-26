-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:14.412124+00:00
-- url     : https://prove2.me/submissions/9a744a1c-92fe-4e95-b99d-49162e4ffc08

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution {S : Set ℕ} {n : ℕ} :
    n ∈ collatzPullback S ↔ (Terras.T^[Nat.log 2 n]) n ∈ S :=
  Iff.rfl
end CollatzEndpointTransport.QuantitativeDensity
