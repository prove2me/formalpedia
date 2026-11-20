-- Prove2me | solution 1 for DeletionCode.BlockAdjunction.blockOf_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:34.339481+00:00
-- url     : https://prove2.me/submissions/6a33de07-d60f-447e-be2f-67c60ea1e5cd

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
import Theorems.Thm_DeletionCode_BlockAdjunction_path_within_block
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf



set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
namespace DeletionCode.BlockAdjunction
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) : Connected (blockOf U a) := by
  intro b hb c hc
  have hab := ((mem_blockOf U a b).mp hb).2
  have hac := ((mem_blockOf U a c).mp hc).2
  exact path_within_block U
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hac) a hab
end DeletionCode.BlockAdjunction
