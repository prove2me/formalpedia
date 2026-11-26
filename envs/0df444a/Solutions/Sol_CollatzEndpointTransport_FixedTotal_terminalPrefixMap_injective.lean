-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalPrefixMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:30.934802+00:00
-- url     : https://prove2.me/submissions/ef05972f-7cf5-4ab1-bf92-4e23fa2ff382

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_initialBlocks_append_terminalBlocks
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
    {N s r : ℕ} (d : List ℕ) :
    Function.Injective (terminalPrefixMap (N := N) (s := s) (r := r) d) := by
  intro c₁ c₂ h
  apply Subtype.ext
  apply Composition.ext
  have hblocks := congrArg (fun p => p.1.blocks) h
  have hc₁ := (mem_terminalFiber_iff.mp c₁.2)
  have hc₂ := (mem_terminalFiber_iff.mp c₂.2)
  have hinit : initialBlocks c₁.1 r = initialBlocks c₂.1 r := by
    simpa [terminalPrefixMap, initialComposition] using hblocks
  calc
    c₁.1.blocks = initialBlocks c₁.1 r ++ terminalBlocks c₁.1 r :=
      (initialBlocks_append_terminalBlocks c₁.1 r).symm
    _ = initialBlocks c₂.1 r ++ terminalBlocks c₂.1 r := by
      rw [hinit, hc₁.2, hc₂.2]
    _ = c₂.1.blocks := initialBlocks_append_terminalBlocks c₂.1 r
end CollatzEndpointTransport.FixedTotal
