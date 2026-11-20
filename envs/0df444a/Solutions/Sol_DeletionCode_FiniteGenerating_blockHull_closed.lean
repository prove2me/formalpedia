-- Prove2me | solution 1 for DeletionCode.FiniteGenerating.blockHull_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:26:02.789049+00:00
-- url     : https://prove2.me/submissions/62b5b2a7-cb15-4fdb-9a9f-3c7f234cc3ee

import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_BlockAdjunction
import Definitions.Def_DeletionCode_FiniteGenerating
import Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_closed


set_option autoImplicit true
open DeletionCode DeletionCode.FiniteGenerating
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks BlockPartition
namespace DeletionCode.FiniteGenerating
theorem _root_.solution {k : ℕ} (G I : RuleSet k) :
    ClosedIn G (RelationBlockSavings.blockHull G I) := by
  intro a ha b _ hab
  exact RelationBlockSavings.blockHull_closed G I ha hab
end DeletionCode.FiniteGenerating
