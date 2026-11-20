-- Prove2me | solution 1 for DeletionCode.BlockAdjunction.new_block_component_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:30.613159+00:00
-- url     : https://prove2.me/submissions/1b99ce04-0fee-4f2f-9ef4-d215c7bf1e47

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
import Theorems.Thm_DeletionCode_BlockAdjunction_blockOf_connected
import Theorems.Thm_DeletionCode_BlockPartition_blockOf_nonempty
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_connected_block_bound
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks



set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
namespace DeletionCode.BlockAdjunction
theorem _root_.solution {t k : ℕ} (ht : 1 ≤ t) (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hcatalogue : ∀ u ∈ U, CatalogueRule t k u) :
    componentCount (blockOf (insert w U) w) ≤
      (2 * t - 1) * (blockOf (insert w U) w).card + 1 := by
  apply connected_block_bound ht _
    (blockOf_nonempty (insert w U) w (Finset.mem_insert_self _ _))
  · intro u hu
    have huNew := ((mem_blockOf (insert w U) w u).mp hu).1
    rcases Finset.mem_insert.mp huNew with huw | huOld
    · simpa only [huw] using hw
    · exact hcatalogue u huOld
  · exact blockOf_connected (insert w U) w
end DeletionCode.BlockAdjunction
