-- Prove2me | solution 1 for DeletionCode.AnchorRecords.decodeFrom_encodeFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:57:44.924331+00:00
-- url     : https://prove2.me/submissions/cf74b30e-823c-429c-bf60-fc91aa9b0912

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_encodeFrom_anchor_bounds
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


section
namespace DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
private theorem decodeFrom_matched (m : ℕ) (bit : Bool) (source : List Bool)
    (packets : List Packet) (hanchor : ∀ p ∈ packets, m + 1 ≤ p.1) :
    decodeFrom m (bit :: source) packets = bit :: decodeFrom (m + 1) source packets := by
  cases packets with
  | nil => rfl
  | cons packet rest =>
    obtain ⟨anchor, side, inserted⟩ := packet
    have ha : m + 1 ≤ anchor := hanchor _ (List.mem_cons_self ..)
    have hgap : anchor - m = (anchor - (m + 1)) + 1 := by omega
    cases side <;> simp [decodeFrom, hgap, Nat.add_assoc]
end DeletionCode.AnchorRecords
end

set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace) (m : ℕ) :
    decodeFrom m trace.source (encodeFrom m trace) = trace.target := by
  induction trace generalizing m with
  | nil => rfl
  | cons col rest ih =>
    cases col with
    | matched bit =>
      change decodeFrom m (bit :: Trace.source rest) (encodeFrom (m + 1) rest) =
        bit :: Trace.target rest
      rw [decodeFrom_matched m bit (Trace.source rest) (encodeFrom (m + 1) rest)
        (fun p hp => (encodeFrom_anchor_bounds rest (m + 1) p hp).1), ih]
    | deletion bit =>
      simp [encodeFrom, decodeFrom, Trace.source, Trace.target, ih]
    | insertion bit =>
      simp [encodeFrom, decodeFrom, Trace.source, Trace.target, ih]
end DeletionCode.AnchorRecords
