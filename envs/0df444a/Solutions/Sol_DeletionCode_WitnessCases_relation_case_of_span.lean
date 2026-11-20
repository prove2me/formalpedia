-- Prove2me | solution 1 for DeletionCode.WitnessCases.relation_case_of_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:48:29.803163+00:00
-- url     : https://prove2.me/submissions/6d0cb1ba-e234-45dd-a3cd-f87d6805ef63

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
import Definitions.Def_DeletionCode_WitnessCases
import Theorems.Thm_DeletionCode_WitnessCases_relation_case
import Theorems.Thm_DeletionCode_CatalogueAlgebra_new_relation_support
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_subset


set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCases
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition FiniteGenerating FiniteRelationBlocks CatalogueAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessCases
theorem _root_.solution {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G : RuleSet k) (hgen : GeneratingAt v G)
    (hcat : ∀ u ∈ G, CatalogueRule t k u) (hK : ∀ u ∈ G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ U : RuleSet k, U ⊆ G ∧ Witness t k v K U := by
  obtain ⟨I, hIG, hI, a, ha, hrel⟩ := new_relation_support (by omega : 1 ≤ t)
    G hcat w hw hnew hspan
  exact ⟨_, RelationBlockSavings.blockHull_subset G I,
    relation_case ht v K G I hIG hI hgen hcat hK hsize w hw a ha hrel⟩
end DeletionCode.WitnessCases
