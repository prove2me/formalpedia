-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.blockHull_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:55.312561+00:00
-- url     : https://prove2.me/submissions/f5db565b-be82-4d73-8aff-aef05ebac5b2

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {k : ℕ} (G I : RuleSet k) : blockHull G I ⊆ G := by
  classical
  exact Finset.filter_subset _ _
end DeletionCode.RelationBlockSavings
