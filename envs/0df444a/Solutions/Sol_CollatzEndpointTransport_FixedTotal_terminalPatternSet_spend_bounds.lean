-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:35:48.272127+00:00
-- url     : https://prove2.me/submissions/873e6c53-e297-4107-825d-aae4bb158674

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_initialBlocks_append_terminalBlocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalBlocks_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalBlocks_pos
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
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r D : ℕ} (hrs : r ≤ s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    r ≤ D ∧ s - r ≤ N - D := by
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, hdc⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  have hdLength : d.length = r := by
    rw [← hdc]
    exact terminalBlocks_length c (by simpa [hcLength] using hrs)
  have hdPos : ∀ i ∈ d, 1 ≤ i := by
    intro i hi
    rw [← hdc] at hi
    exact terminalBlocks_pos c r i hi
  have hterminal := List.length_le_sum_of_one_le d hdPos
  have hinitialPos : ∀ i ∈ initialBlocks c r, 1 ≤ i := by
    intro i hi
    exact c.blocks_pos (List.mem_of_mem_take hi)
  have hinitial :=
    List.length_le_sum_of_one_le (initialBlocks c r) hinitialPos
  have hsum := congrArg List.sum (initialBlocks_append_terminalBlocks c r)
  simp only [List.sum_append, c.blocks_sum] at hsum
  rw [initialBlocks_length, hcLength] at hinitial
  rw [hdLength, hdSum] at hterminal
  rw [hdc, hdSum] at hsum
  omega
end CollatzEndpointTransport.FixedTotal
