-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.edge_in_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:53.982013+00:00
-- url     : https://prove2.me/submissions/88819c45-9d0f-4f24-afb7-18200a4a7fbb

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_SupportBlockCount_edge_block_witness
import Theorems.Thm_DeletionCode_BlockPartition_blocks_support_disjoint
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {k : ℕ} (G B : RuleSet k) (hB : B ∈ blocks G)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v)
    (hu : Incident B u) : RuleSetEdge B u v := by
  classical
  obtain ⟨C, hC, heC, huC, _⟩ := edge_block_witness G he
  have hBC : B = C := by
    by_contra hne
    exact blocks_support_disjoint G B hB C hC hne u hu huC
  simpa only [hBC] using heC
end DeletionCode.SupportBlockCount
