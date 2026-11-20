-- Prove2me | solution 1 for DeletionCode.BlockPartition.blockOf_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:11.378456+00:00
-- url     : https://prove2.me/submissions/37bf5e1b-c664-482f-83c5-a64220bef956

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (a : Gram (windowLength k) → ℤ) (ha : a ∈ U) : (blockOf U a).Nonempty := by
  refine ⟨a, (mem_blockOf U a a).mpr ⟨ha, ?_⟩⟩
  exact Relation.EqvGen.refl _
end DeletionCode.BlockPartition
