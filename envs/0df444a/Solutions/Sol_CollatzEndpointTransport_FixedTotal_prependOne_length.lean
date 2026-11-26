-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.prependOne_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:38.413069+00:00
-- url     : https://prove2.me/submissions/b5492937-cddd-4667-aaa1-ed7e8de5d3e0

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil


attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} (c : Composition N) :
    (prependOne c).length = c.length + 1 := by
  simp [Composition.length, prependOne]
end CollatzEndpointTransport.FixedTotal
