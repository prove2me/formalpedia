-- Prove2me | solution 1 for DeletionCode.BlockAdjunction.new_block_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:53.427966+00:00
-- url     : https://prove2.me/submissions/136a5b15-6e77-43ae-9b15-897d6b87c68e

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
import Theorems.Thm_DeletionCode_BlockAdjunction_blockOf_insert_eq
import Theorems.Thm_DeletionCode_BlockPartition_attached_blocks_union_bound
import Theorems.Thm_DeletionCode_CatalogueVertexBound_catalogue_vertex_card_le


set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
namespace DeletionCode.BlockAdjunction
theorem _root_.solution {t k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hsize : ∀ B ∈ blocks U, B.card ≤ windowLength k) :
    (blockOf (insert w U) w).card ≤ 1 + 4 * t * (windowLength k) ^ 2 := by
  rw [blockOf_insert_eq]
  exact attached_blocks_union_bound U w t (windowLength k) hsize
    (CatalogueVertexBound.catalogue_vertex_card_le w hw)
end DeletionCode.BlockAdjunction
