-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.relation_block_hull_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:41:39.188613+00:00
-- url     : https://prove2.me/submissions/65b0d114-e056-453f-95ad-23b30bf80cd5

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_RelationBlockSavings_relation_seeded_bound
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_subset
import Theorems.Thm_DeletionCode_RelationBlockSavings_subset_blockHull
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_covered
import Theorems.Thm_DeletionCode_GeneratingBlocks_subset_blockHull


set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {t k : ℕ} (ht : 2 ≤ t) (G I : RuleSet k)
    (hIG : I ⊆ G) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount (blockHull G I) ≤ (2 * t - 1) * (blockHull G I).card := by
  exact relation_seeded_bound ht (blockHull G I) I (subset_blockHull G I hIG) hI
    (fun u hu => hcat u (blockHull_subset G I hu)) (blockHull_covered G I hIG)
    w hw a ha hrel
end DeletionCode.RelationBlockSavings
