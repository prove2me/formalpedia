-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.subset_blockHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:56.402729+00:00
-- url     : https://prove2.me/submissions/ff35dc27-81c7-4150-97e7-d833a87f6375

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) : I ⊆ blockHull G I := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨hIG hi, i, hi, Relation.EqvGen.refl i⟩
end DeletionCode.RelationBlockSavings
