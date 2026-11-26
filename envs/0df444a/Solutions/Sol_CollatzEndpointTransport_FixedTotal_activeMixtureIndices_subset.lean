-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.activeMixtureIndices_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:16.806146+00:00
-- url     : https://prove2.me/submissions/cf19bd58-d303-40ff-b02a-a4e1cc7c311e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {iota : Type*} {alpha : iota → Type*}
    (U : Finset iota) (W : ∀ i, Finset (alpha i)) :
    activeMixtureIndices U W ⊆ U := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1
end CollatzEndpointTransport.FixedTotal
