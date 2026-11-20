-- Prove2me | solution 1 for DeletionCode.LargeBlockSelection.blockOf_insert_subset_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:03.64148+00:00
-- url     : https://prove2.me/submissions/2cb47598-24f8-4dc2-a886-4ba18ae7eb22

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
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
    (w a : Gram (windowLength k) → ℤ)
    (hw : w ∉ blockOf (insert w G) a) : blockOf (insert w G) a ⊆ G := by
  classical
  intro b hb
  have hbNew := ((mem_blockOf (insert w G) a b).mp hb).1
  rcases Finset.mem_insert.mp hbNew with hbw | hbG
  · exact False.elim (hw (by simpa only [hbw] using hb))
  · exact hbG
end DeletionCode.LargeBlockSelection
