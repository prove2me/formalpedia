-- Prove2me | solution 1 for DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:34.46632+00:00
-- url     : https://prove2.me/submissions/7d65ab80-d8ba-4339-8dd0-94cc30fc8e49

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
namespace DeletionCode.FiniteRelationBlocks
theorem _root_.solution {k : ℕ} (G I B : RuleSet k) :
    B ∈ selectedBlocks G I ↔ B ∈ blocks G ∧ (B ∩ I).Nonempty := by
  classical
  simp [selectedBlocks]
end DeletionCode.FiniteRelationBlocks
