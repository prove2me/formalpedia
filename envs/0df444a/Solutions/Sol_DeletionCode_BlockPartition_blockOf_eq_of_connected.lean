-- Prove2me | solution 1 for DeletionCode.BlockPartition.blockOf_eq_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:38.473244+00:00
-- url     : https://prove2.me/submissions/0b76550e-dfd0-4507-a2c7-8a8efdcbc574

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm

attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) (hab : ConnectedIn U a b) :
    blockOf U a = blockOf U b := by
  classical
  ext c
  simp only [mem_blockOf]
  constructor
  · rintro ⟨hc, hac⟩
    exact ⟨hc, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hac⟩
  · rintro ⟨hc, hbc⟩
    exact ⟨hc, Relation.EqvGen.trans _ _ _ hab hbc⟩
end DeletionCode.BlockPartition
