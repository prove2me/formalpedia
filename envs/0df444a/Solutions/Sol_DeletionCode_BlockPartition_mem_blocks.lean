-- Prove2me | solution 1 for DeletionCode.BlockPartition.mem_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:08.925857+00:00
-- url     : https://prove2.me/submissions/375a83b7-376d-4c7a-a4f7-69b2291f1d4a

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U B : RuleSet k) :
    B ∈ blocks U ↔ ∃ a ∈ U, blockOf U a = B := by
  classical
  simp [blocks]
end DeletionCode.BlockPartition
