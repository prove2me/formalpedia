-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.blockHull_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:26.068458+00:00
-- url     : https://prove2.me/submissions/c935fe34-83d2-4e2d-97b1-d687c3b583d5

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_RelationBlockSavings_subset_blockHull
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_closed
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_GeneratingBlocks_blockHull_closed
import Theorems.Thm_DeletionCode_GeneratingBlocks_subset_blockHull

section
namespace DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
private theorem blockHull_path {k : ℕ} (G I : RuleSet k)
    {a b : Gram (windowLength k) → ℤ}
    (hpath : Relation.EqvGen (FiniteConnectedGrowth.Induced G RuleAdjacent) a b) :
    a ∈ blockHull G I →
      Relation.EqvGen (FiniteConnectedGrowth.Induced (blockHull G I) RuleAdjacent) a b := by
  induction hpath with
  | rel a b hab =>
    intro ha
    exact Relation.EqvGen.rel a b
      ⟨ha, blockHull_closed G I ha (Relation.EqvGen.rel a b hab), hab.2.2⟩
  | refl a => intro _; exact Relation.EqvGen.refl a
  | symm a b h ih =>
    intro hb
    have ha := blockHull_closed G I hb (Relation.EqvGen.symm a b h)
    exact Relation.EqvGen.symm a b (ih ha)
  | trans a b c hab hbc ihab ihbc =>
    intro ha
    exact Relation.EqvGen.trans a b c (ihab ha) (ihbc (blockHull_closed G I ha hab))
end DeletionCode.RelationBlockSavings
end

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G) :
    ∀ u ∈ blockHull G I, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced (blockHull G I) RuleAdjacent) i u := by
  classical
  intro u hu
  obtain ⟨_, i, hi, hpath⟩ := Finset.mem_filter.mp hu
  exact ⟨i, hi, blockHull_path G I hpath (subset_blockHull G I hIG hi)⟩
end DeletionCode.RelationBlockSavings
