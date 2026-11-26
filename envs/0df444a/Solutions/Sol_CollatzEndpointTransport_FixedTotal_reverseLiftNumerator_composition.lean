-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_composition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:27.222618+00:00
-- url     : https://prove2.me/submissions/0a07cf73-7866-4c7b-9e89-39ff59695893

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_reverse_eq

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} (c : Composition N) :
    reverseLiftNumerator c.blocks.reverse =
      3 ^ c.length + syracuseNumerator c := by
  exact reverseLiftNumerator_reverse_eq c.blocks
end CollatzEndpointTransport.FixedTotal
