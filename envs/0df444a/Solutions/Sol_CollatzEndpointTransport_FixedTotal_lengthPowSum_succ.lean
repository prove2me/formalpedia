-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.lengthPowSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:56.710544+00:00
-- url     : https://prove2.me/submissions/6c7873f5-2384-400f-9dd1-920329727135

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
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    lengthPowSum (N + 1) = 4 * lengthPowSum N := by
  let e := compositionSuccEquiv N hN
  have he :=
    (Equiv.sum_comp e (fun c : Composition (N + 1) => 3 ^ c.length)).symm
  rw [Fintype.sum_sum_type] at he
  dsimp [e, compositionSuccEquiv] at he
  change lengthPowSum (N + 1) = _ at he
  rw [he]
  simp only [increaseFirst_length, prependOne_length, pow_succ]
  rw [← Finset.sum_mul]
  change lengthPowSum N + lengthPowSum N * 3 = 4 * lengthPowSum N
  omega
end CollatzEndpointTransport.FixedTotal
