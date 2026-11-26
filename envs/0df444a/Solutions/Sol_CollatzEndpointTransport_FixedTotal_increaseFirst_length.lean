-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.increaseFirst_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:22:54.039894+00:00
-- url     : https://prove2.me/submissions/b2fa058d-5912-48ee-b29d-bf568031fd49

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil


attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    (increaseFirst hN c).length = c.length := by
  have hcne := composition_blocks_ne_nil hN c
  cases hc : c.blocks with
  | nil => exact False.elim (hcne hc)
  | cons k ks =>
      simp [Composition.length, increaseFirst, hc]
end CollatzEndpointTransport.FixedTotal
