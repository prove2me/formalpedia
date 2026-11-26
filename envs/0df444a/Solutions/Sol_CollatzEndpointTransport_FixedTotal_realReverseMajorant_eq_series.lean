-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.realReverseMajorant_eq_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:00.012807+00:00
-- url     : https://prove2.me/submissions/2ea5804f-9267-44f5-be28-0e71e93cf80d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_eq_series
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_coe_reverseMomentTerm_eq_realReverseMomentTerm
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


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} (theta : ℝ) (c : Composition N)
    (hc : c ∈ fixedSet N s) :
    realReverseMajorant theta c =
      (∑ r ∈ Ico 1 (s + 1), realReverseMomentTerm theta c r) +
        (((3 : ℝ) ^ theta) ^ s /
          (((2 : ℝ) ^ N) ^ theta)) := by
  have hlen : c.length = s := (Finset.mem_filter.mp hc).2
  have hsum : c.blocks.sum = N := c.blocks_sum
  unfold realReverseMajorant
  rw [reverseMomentMajorant_eq_series]
  unfold reverseMomentSeries
  push_cast
  rw [List.length_reverse, c.blocks_length, hlen,
    List.sum_reverse, hsum]
  rw [Finset.sum_Ico_eq_sum_range]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro i hi
    have hir : 0 < i + 1 := Nat.succ_pos i
    simpa [Nat.add_comm] using
      (coe_reverseMomentTerm_eq_realReverseMomentTerm
        (theta := theta) c (r := i + 1) hir)
  · rfl
end CollatzEndpointTransport.FixedTotal
