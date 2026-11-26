-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.lowerLengthPowSum_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:41.931953+00:00
-- url     : https://prove2.me/submissions/e7074a4d-3603-4b43-a1be-2a1244990b16

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_lengthPowSum_formula
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
    (∑ c : Composition N, 3 ^ (c.length - 1)) = 4 ^ (N - 1) := by
  have hpoint :
      ∀ c : Composition N,
        3 * 3 ^ (c.length - 1) = 3 ^ c.length := by
    intro c
    have hlen := c.length_pos_of_pos hN
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
    rw [hj]
    simp [pow_succ, mul_comm]
  have hsum :
      3 * (∑ c : Composition N, 3 ^ (c.length - 1)) =
        lengthPowSum N := by
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    exact hpoint
  rw [lengthPowSum_formula N hN] at hsum
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hsum
end CollatzEndpointTransport.FixedTotal
