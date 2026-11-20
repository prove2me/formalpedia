-- Prove2me | solution 1 for DeletionCode.FiniteGenerating.generating_blockOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:26:41.232177+00:00
-- url     : https://prove2.me/submissions/e8d93ca6-dcaa-416d-9a38-2e970c3f0454

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_FiniteGenerating_GeneratingAt_restrict
import Theorems.Thm_DeletionCode_FiniteGenerating_blockOf_closed
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf



set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
namespace DeletionCode.FiniteGenerating
theorem _root_.solution {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (a : Gram (windowLength k) → ℤ) :
    GeneratingAt v (blockOf G a) := by
  apply hgen.restrict
  · intro u hu
    exact ((mem_blockOf G a u).mp hu).1
  · exact blockOf_closed G a
end DeletionCode.FiniteGenerating
