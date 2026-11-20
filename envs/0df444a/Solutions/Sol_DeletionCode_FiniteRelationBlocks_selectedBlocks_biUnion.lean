-- Prove2me | solution 1 for DeletionCode.FiniteRelationBlocks.selectedBlocks_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:59.61351+00:00
-- url     : https://prove2.me/submissions/9bb69d1a-804b-4fb6-98be-3c0b5fd047f6

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_subset
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
namespace DeletionCode.FiniteRelationBlocks
theorem _root_.solution {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) :
    (selectedBlocks G I).biUnion id = RelationBlockSavings.blockHull G I := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨B, hB, huB⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨hBblock, i, hi⟩ := (mem_selectedBlocks G I B).mp hB
    obtain ⟨hiB, hiI⟩ := Finset.mem_inter.mp hi
    obtain ⟨r, _, hr⟩ := (mem_blocks G B).mp hBblock
    have hui := (mem_blockOf G r u).mp (by simpa only [hr, id_eq] using huB)
    have hii := (mem_blockOf G r i).mp (by simpa only [hr] using hiB)
    apply Finset.mem_filter.mpr
    exact ⟨hui.1, i, hiI, Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hii.2) hui.2⟩
  · intro hu
    obtain ⟨_, i, hiI, hiu⟩ := Finset.mem_filter.mp hu
    have hiG := hIG hiI
    have hiB : i ∈ blockOf G i :=
      (mem_blockOf G i i).mpr ⟨hiG, Relation.EqvGen.refl i⟩
    have hB : blockOf G i ∈ selectedBlocks G I :=
      (mem_selectedBlocks G I (blockOf G i)).mpr
        ⟨(mem_blocks G (blockOf G i)).mpr ⟨i, hiG, rfl⟩,
          i, Finset.mem_inter.mpr ⟨hiB, hiI⟩⟩
    exact Finset.mem_biUnion.mpr ⟨blockOf G i, hB,
      (mem_blockOf G i u).mpr ⟨(RelationBlockSavings.blockHull_subset G I hu), hiu⟩⟩
end DeletionCode.FiniteRelationBlocks
