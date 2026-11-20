-- Prove2me | solution 1 for DeletionCode.LargeBlockSelection.block_not_containing_new_is_old
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:26:09.183896+00:00
-- url     : https://prove2.me/submissions/0a203e32-99af-4cf9-95f6-d3cd97456204

import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_LargeBlockSelection
import Theorems.Thm_DeletionCode_LargeBlockSelection_blockOf_insert_subset_of_not_mem
import Theorems.Thm_DeletionCode_LargeBlockSelection_blockOf_insert_eq_of_not_mem
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
    (hB : B ∈ blocks (insert w G)) (hw : w ∉ B) : B ∈ blocks G := by
  classical
  obtain ⟨a, ha, hvalue⟩ := (mem_blocks (insert w G) B).mp hB
  have hw' : w ∉ blockOf (insert w G) a := by simpa only [hvalue] using hw
  have haBlock : a ∈ blockOf (insert w G) a :=
    (mem_blockOf (insert w G) a a).mpr ⟨ha, Relation.EqvGen.refl a⟩
  have haG := blockOf_insert_subset_of_not_mem G w a hw' haBlock
  exact (mem_blocks G B).mpr
    ⟨a, haG, (blockOf_insert_eq_of_not_mem G w a hw').symm.trans hvalue⟩
end DeletionCode.LargeBlockSelection
