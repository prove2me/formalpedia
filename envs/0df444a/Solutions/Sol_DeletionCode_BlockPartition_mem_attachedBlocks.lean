-- Prove2me | solution 1 for DeletionCode.BlockPartition.mem_attachedBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:37.272291+00:00
-- url     : https://prove2.me/submissions/70fce2ef-477b-4058-add0-c25673211e53

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U B : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    B ∈ attachedBlocks U w ↔
      B ∈ blocks U ∧ ∃ v, Incident B v ∧ Incident {w} v := by
  classical
  simp [attachedBlocks]
end DeletionCode.BlockPartition
