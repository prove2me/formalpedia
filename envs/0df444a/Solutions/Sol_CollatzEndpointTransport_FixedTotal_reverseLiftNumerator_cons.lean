-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:27.323691+00:00
-- url     : https://prove2.me/submissions/06c8c237-ba31-4e2a-8c07-3a08b190c116

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (k : ℕ) (ks : List ℕ) :
    reverseLiftNumerator (k :: ks) =
      3 * reverseLiftNumerator ks + 2 ^ ks.sum := rfl
end CollatzEndpointTransport.FixedTotal
