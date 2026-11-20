-- Prove2me | solution 1 for DeletionCode.LargeBlockSelection.block_containing_new_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:05.392246+00:00
-- url     : https://prove2.me/submissions/f32be82f-25de-4da1-93c0-1081cb3f8cc0

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
import Theorems.Thm_DeletionCode_BlockPartition_blockOf_eq_of_connected
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks



set_option autoImplicit true
open DeletionCode DeletionCode.LargeBlockSelection
open HeaderRecovery SignedSupport SignedRuleCount BlockPartition BlockAdjunction
namespace DeletionCode.LargeBlockSelection
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (B : RuleSet k)
    (hB : B ∈ blocks (insert w G)) (hw : w ∈ B) :
    B = blockOf (insert w G) w := by
  classical
  obtain ⟨a, _, hvalue⟩ := (mem_blocks (insert w G) B).mp hB
  have hw' : w ∈ blockOf (insert w G) a := by simpa only [hvalue] using hw
  have haw := ((mem_blockOf (insert w G) a w).mp hw').2
  exact hvalue.symm.trans (blockOf_eq_of_connected (insert w G) a w haw)
end DeletionCode.LargeBlockSelection
