-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.edge_block_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:39.001818+00:00
-- url     : https://prove2.me/submissions/ee44cf7f-8db9-49a1-b08b-1a2ff9e53b2e

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks



set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {k : ℕ} (G : RuleSet k)
    {u v : Vertex (windowLength k)} (he : RuleSetEdge G u v) :
    ∃ B ∈ blocks G, RuleSetEdge B u v ∧ Incident B u ∧ Incident B v := by
  obtain ⟨w, hw, g, hg, hu, hv⟩ := he
  have hwin : w ∈ blockOf G w :=
    (mem_blockOf G w w).mpr ⟨hw, Relation.EqvGen.refl _⟩
  have hblock : blockOf G w ∈ blocks G :=
    (mem_blocks G (blockOf G w)).mpr ⟨w, hw, rfl⟩
  have hedge : RuleSetEdge (blockOf G w) u v := ⟨w, hwin, g, hg, hu, hv⟩
  exact ⟨blockOf G w, hblock, hedge, ⟨v, Or.inl hedge⟩, ⟨u, Or.inr hedge⟩⟩
end DeletionCode.SupportBlockCount
