-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.composition_one_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:25.507618+00:00
-- url     : https://prove2.me/submissions/b02d8d01-4636-4d66-90d6-f1968521bf75

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (c : Composition 1) :
    c.blocks = [1] := by
  have hlenPos := c.length_pos_of_pos (by norm_num)
  have hlenLe := c.length_le
  have hlen : c.length = 1 := by omega
  cases hc : c.blocks with
  | nil =>
      have := c.blocks_sum
      simp [hc] at this
  | cons k ks =>
      have hks : ks = [] := by
        have : (k :: ks).length = 1 := by
          simpa [Composition.length, hc] using hlen
        simp only [List.length_cons] at this
        exact List.length_eq_zero_iff.mp (Nat.succ.inj this)
      subst ks
      have hsum := c.blocks_sum
      simp [hc] at hsum
      subst k
      rfl
end CollatzEndpointTransport.FixedTotal
