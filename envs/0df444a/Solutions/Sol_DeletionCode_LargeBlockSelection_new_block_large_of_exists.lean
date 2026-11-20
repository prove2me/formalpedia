-- Prove2me | solution 1 for DeletionCode.LargeBlockSelection.new_block_large_of_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:30:54.766303+00:00
-- url     : https://prove2.me/submissions/3ed2b0eb-194c-4524-8466-0078eca88840

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
import Theorems.Thm_DeletionCode_LargeBlockSelection_oversized_block_eq_new_block
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks



set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction
namespace DeletionCode.LargeBlockSelection
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (L : ℕ)
    (hsize : ∀ B ∈ blocks G, B.card ≤ L)
    (hlarge : ∃ B ∈ blocks (insert w G), L < B.card) :
    L < (blockOf (insert w G) w).card := by
  obtain ⟨B, hB, hcard⟩ := hlarge
  simpa only [oversized_block_eq_new_block G w L hsize B hB hcard] using hcard
end DeletionCode.LargeBlockSelection
