-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalPatternSet_subset_fixedBlockSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:03.349973+00:00
-- url     : https://prove2.me/submissions/644bc567-ee61-47bd-8700-384ff374f8d4

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
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
    {N s r D : ℕ} (hr : r ≤ s) :
    terminalPatternSet N s r D ⊆ fixedBlockSet D r := by
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, rfl⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  let suffix : Composition D := {
    blocks := terminalBlocks c r
    blocks_pos := by
      intro x hx
      exact terminalBlocks_pos c r x hx
    blocks_sum := hdSum
  }
  apply Finset.mem_image.mpr
  refine ⟨suffix, ?_, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change (terminalBlocks c r).length = r
  exact terminalBlocks_length c (by simpa [hcLength] using hr)
  · rfl
end CollatzEndpointTransport.FixedTotal
