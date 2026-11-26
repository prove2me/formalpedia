-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fixedSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:04:09.624385+00:00
-- url     : https://prove2.me/submissions/2b56774d-56ac-4106-8210-146d10c698c2

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
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
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (f : Composition N → ℕ) :
    (∑ s ∈ Finset.Icc 1 N, ∑ c ∈ fixedSet N s, f c) =
      ∑ c : Composition N, f c := by
  have hmap :
      ∀ c ∈ (Finset.univ : Finset (Composition N)),
        c.length ∈ Finset.Icc 1 N := by
    intro c hc
    exact Finset.mem_Icc.mpr
      ⟨c.length_pos_of_pos hN, c.length_le⟩
  simpa [fixedSet] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Composition N)))
      (t := Finset.Icc 1 N)
      (g := fun c : Composition N => c.length)
      hmap f)
end CollatzEndpointTransport.FixedTotal
