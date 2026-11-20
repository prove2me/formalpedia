-- Prove2me | solution 1 for DeletionCode.SupportBlockCount.attached_blocks_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:33:04.578933+00:00
-- url     : https://prove2.me/submissions/30e1198a-d9a6-40eb-8f83-0d0d54cacdd4

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_SupportBlockCount
import Theorems.Thm_DeletionCode_SupportBlockCount_catalogue_block_count_le
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks



set_option autoImplicit true
open DeletionCode DeletionCode.SupportBlockCount
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition SupportComponents
namespace DeletionCode.SupportBlockCount
theorem _root_.solution {t k : ℕ} (G : RuleSet k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hsub : SupportInclusion.CoordinateSupportIncluded {w} G) :
    (attachedBlocks G w).card ≤ 2 * t := by
  apply catalogue_block_count_le G w (attachedBlocks G w) hw
  · intro B hB
    exact ((mem_attachedBlocks G B w).mp hB).1
  · exact hsub
  · intro B hB
    exact ((mem_attachedBlocks G B w).mp hB).2
end DeletionCode.SupportBlockCount
