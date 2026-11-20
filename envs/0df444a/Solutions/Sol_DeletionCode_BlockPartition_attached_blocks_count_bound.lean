-- Prove2me | solution 1 for DeletionCode.BlockPartition.attached_blocks_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:55.323858+00:00
-- url     : https://prove2.me/submissions/8619dc10-b1d3-4021-a363-320332cf6700

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_blocks_support_disjoint
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_AttachedBlocks_attached_block_count_le_vertices

attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    (attachedBlocks U w).card ≤ Fintype.card (RuleSetVertex {w}) := by
  apply AttachedBlocks.attached_block_count_le_vertices
  · intro B hB
    exact ((mem_attachedBlocks U B w).mp hB).2
  · intro B hB C hC hne
    exact blocks_support_disjoint U B ((mem_attachedBlocks U B w).mp hB).1
      C ((mem_attachedBlocks U C w).mp hC).1 hne
end DeletionCode.BlockPartition
