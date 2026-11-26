-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.subsetMomentExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:13.950853+00:00
-- url     : https://prove2.me/submissions/e085d99b-9797-4acc-91a1-78c341c9d2c2

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_powerset_pow_card
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
open scoped Real
noncomputable section
variable {α : Type*} [DecidableEq α]
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (U S : Finset α) (t : ℝ) :
    (1 + t) ^ (U ∩ S).card =
      ∑ J ∈ U.powerset, if J ⊆ S then t ^ J.card else 0 := by
  classical
  rw [← sum_powerset_pow_card (U ∩ S) t]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext J
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro h
      exact ⟨fun x hx => (Finset.mem_inter.mp (h hx)).1,
        fun x hx => (Finset.mem_inter.mp (h hx)).2⟩
    · rintro ⟨hJU, hJS⟩
      exact fun x hx => Finset.mem_inter.mpr ⟨hJU hx, hJS hx⟩
  · intro J hJ
    rfl
end CollatzEndpointTransport.FixedTotal
