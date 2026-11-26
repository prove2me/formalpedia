-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.hypergeometricChooseMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:28.525671+00:00
-- url     : https://prove2.me/submissions/90768d7f-74a0-4c3e-9530-ff5fda3a6dda

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeHypergeometricMoment_le
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
    (∑ j ∈ range (m + 1),
        if _hjk : j ≤ k then
          (m.choose j : ℝ) * ((n - m).choose (k - j) : ℝ) *
            (1 + t) ^ j
        else 0) / (n.choose k : ℝ) ≤
      (1 + ((k : ℝ) / n) * t) ^ m := by
  have hsubset : range m ⊆ range n :=
    Finset.range_subset_range.mpr hmn
  have hnonempty : (range n).Nonempty := by
    exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)
  simpa using
    (fixedSizeHypergeometricMoment_le
      (V := range n) (U := range m) (k := k) (t := t)
      hsubset (by simpa using hkn) hnonempty ht)
end CollatzEndpointTransport.FixedTotal
