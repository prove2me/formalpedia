-- Prove2me | solution 1 for DeletionCode.BlockPartition.mem_blockOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:14.989052+00:00
-- url     : https://prove2.me/submissions/012dd282-770f-45a1-a370-592c606a1d9f

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_AttachedBlocks
import Definitions.Def_DeletionCode_BlockPartition

set_option autoImplicit true
open DeletionCode DeletionCode.BlockPartition
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
namespace DeletionCode.BlockPartition
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (a b : Gram (windowLength k) → ℤ) :
    b ∈ blockOf U a ↔ b ∈ U ∧ ConnectedIn U a b := by
  classical
  simp [blockOf]
end DeletionCode.BlockPartition
