-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.hypergeometricChooseMoment_ambient_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:07.334417+00:00
-- url     : https://prove2.me/submissions/2c022a7e-9629-497e-bc43-ef778eaa978d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_hypergeometricChooseMoment_le
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
    {n k m : ℕ} {t : ℝ}
    (hmn : m ≤ n) (hkn : k ≤ n) (hn : 0 < n) (ht : 0 ≤ t) :
    (∑ j ∈ range (n + 1),
        if _hjk : j ≤ k then
          (m.choose j : ℝ) * ((n - m).choose (k - j) : ℝ) *
            (1 + t) ^ j
        else 0) / (n.choose k : ℝ) ≤
      (1 + ((k : ℝ) / n) * t) ^ m := by
  let f : ℕ → ℝ := fun j =>
    if _hjk : j ≤ k then
      (m.choose j : ℝ) * ((n - m).choose (k - j) : ℝ) *
        (1 + t) ^ j
    else 0
  have hsubset : range (m + 1) ⊆ range (n + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hmn)
  have hsum :
      ∑ j ∈ range (m + 1), f j = ∑ j ∈ range (n + 1), f j := by
    apply Finset.sum_subset hsubset
    intro j hj hnot
    have hmj : m < j := by
      have hnotlt : ¬j < m + 1 := by
        simpa only [Finset.mem_range] using hnot
      omega
    simp [f, Nat.choose_eq_zero_of_lt hmj]
  rw [← hsum]
  exact hypergeometricChooseMoment_le hmn hkn hn ht
end CollatzEndpointTransport.FixedTotal
