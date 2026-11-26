-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumerator_increaseFirst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:19.93009+00:00
-- url     : https://prove2.me/submissions/433c5ce5-7164-4e59-b443-d7bfaf8b615b

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil


attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    syracuseNumerator (increaseFirst hN c) + 3 ^ (c.length - 1) =
      2 * syracuseNumerator c := by
  have hcne := composition_blocks_ne_nil hN c
  cases hc : c.blocks with
  | nil => exact False.elim (hcne hc)
  | cons k ks =>
      have hlen : c.length - 1 = ks.length := by
        simp [Composition.length, hc]
      simp only [syracuseNumerator, increaseFirst, hc, List.head_cons,
        List.tail_cons, syracuseNumeratorList]
      rw [hlen]
      rw [pow_succ]
      ring
end CollatzEndpointTransport.FixedTotal
