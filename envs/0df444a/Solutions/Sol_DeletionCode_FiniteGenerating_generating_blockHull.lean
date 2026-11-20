-- Prove2me | solution 1 for DeletionCode.FiniteGenerating.generating_blockHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:18.694524+00:00
-- url     : https://prove2.me/submissions/1fb11b5c-c677-4ecf-8326-48cc6b1c3359

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_FiniteGenerating_GeneratingAt_restrict
import Theorems.Thm_DeletionCode_FiniteGenerating_blockHull_closed
import Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_closed
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_subset


set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
namespace DeletionCode.FiniteGenerating
theorem _root_.solution {k : ℕ} {v : Gram (windowLength k) → ℤ}
    {G : RuleSet k} (hgen : GeneratingAt v G) (I : RuleSet k) :
    GeneratingAt v (RelationBlockSavings.blockHull G I) :=
  hgen.restrict (RelationBlockSavings.blockHull_subset G I) (blockHull_closed G I)
end DeletionCode.FiniteGenerating
