-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.numeratorSum_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:35.139549+00:00
-- url     : https://prove2.me/submissions/992ccccc-80fe-4a01-b0b2-d87ee5ebb0d7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_numeratorSum_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_numeratorSum_succ
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
    2 * numeratorSum N = (N + 1) * 4 ^ (N - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  induction k with
  | zero =>
      simp [numeratorSum_one]
  | succ k ih =>
      rw [numeratorSum_succ (k + 1) (by omega)]
      have ih' := ih (by omega)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at ih' ⊢
      rw [pow_succ]
      calc
        2 * (4 * numeratorSum (k + 1) + 2 * 4 ^ k) =
            4 * (2 * numeratorSum (k + 1)) + 4 * 4 ^ k := by ring
        _ = 4 * ((k + 2) * 4 ^ k) + 4 * 4 ^ k := by rw [ih']
        _ = (k + 3) * (4 ^ k * 4) := by ring
end CollatzEndpointTransport.FixedTotal
