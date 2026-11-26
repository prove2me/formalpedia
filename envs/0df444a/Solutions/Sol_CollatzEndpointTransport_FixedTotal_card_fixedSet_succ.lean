-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_fixedSet_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:23.800501+00:00
-- url     : https://prove2.me/submissions/d6eba1c9-fe28-4809-9e03-22a787983839

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet_eq_indicator_sum
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
    (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    (fixedSet (N + 1) s).card =
      (fixedSet N s).card + (fixedSet N (s - 1)).card := by
  rw [card_fixedSet_eq_indicator_sum, card_fixedSet_eq_indicator_sum,
    card_fixedSet_eq_indicator_sum]
  let e := compositionSuccEquiv N hN
  have he :=
    (Equiv.sum_comp e
      (fun c : Composition (N + 1) => if c.length = s then 1 else 0)).symm
  rw [Fintype.sum_sum_type] at he
  dsimp [e, compositionSuccEquiv] at he
  rw [he]
  simp only [increaseFirst_length, prependOne_length]
  apply congrArg₂ (· + ·) rfl
  apply Fintype.sum_congr
  intro c
  by_cases hlen : c.length + 1 = s
  · have hpred : c.length = s - 1 := by omega
    rw [if_pos hlen, if_pos hpred]
  · have hpred : c.length ≠ s - 1 := by
      intro h
      have hlenPos := c.length_pos_of_pos hN
      omega
    rw [if_neg hlen, if_neg hpred]
end CollatzEndpointTransport.FixedTotal
