-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.numeratorSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:27.865806+00:00
-- url     : https://prove2.me/submissions/589a7c1c-bb49-4c50-9e25-f7c0382ed7f3

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_lowerLengthPowSum_formula
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_child_numerator_sum
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
    numeratorSum (N + 1) =
      4 * numeratorSum N + 2 * 4 ^ (N - 1) := by
  let e := compositionSuccEquiv N hN
  have he :=
    (Equiv.sum_comp e
      (fun c : Composition (N + 1) => syracuseNumerator c)).symm
  rw [Fintype.sum_sum_type] at he
  dsimp [e, compositionSuccEquiv] at he
  change numeratorSum (N + 1) = _ at he
  rw [he]
  have hchildren :
      (∑ c : Composition N, syracuseNumerator (increaseFirst hN c)) +
          ∑ c : Composition N, syracuseNumerator (prependOne c) =
        ∑ c : Composition N,
          (4 * syracuseNumerator c + 2 * 3 ^ (c.length - 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    exact child_numerator_sum hN
  rw [hchildren, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  change
    4 * numeratorSum N +
        2 * (∑ c : Composition N, 3 ^ (c.length - 1)) =
      4 * numeratorSum N + 2 * 4 ^ (N - 1)
  rw [lowerLengthPowSum_formula N hN]
end CollatzEndpointTransport.FixedTotal
