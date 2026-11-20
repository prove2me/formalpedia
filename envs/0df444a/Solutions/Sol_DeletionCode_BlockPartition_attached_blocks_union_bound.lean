-- Prove2me | solution 1 for DeletionCode.BlockPartition.attached_blocks_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:53.470984+00:00
-- url     : https://prove2.me/submissions/3eecb628-cc36-41bf-b909-42e065cb3c2c

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_blocks_support_disjoint
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_AttachedBlocks_attached_union_card_bound_quadratic

attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (t L : ℕ)
    (hsize : ∀ B ∈ blocks U, B.card ≤ L)
    (hvertices : Fintype.card (RuleSetVertex {w}) ≤ 4 * t * L) :
    (insert w ((attachedBlocks U w).biUnion id)).card ≤ 1 + 4 * t * L ^ 2 := by
  apply AttachedBlocks.attached_union_card_bound_quadratic
  · intro B hB
    exact hsize B ((mem_attachedBlocks U B w).mp hB).1
  · intro B hB
    exact ((mem_attachedBlocks U B w).mp hB).2
  · intro B hB C hC hne
    exact blocks_support_disjoint U B ((mem_attachedBlocks U B w).mp hB).1
      C ((mem_attachedBlocks U C w).mp hC).1 hne
  · exact hvertices
end DeletionCode.BlockPartition
