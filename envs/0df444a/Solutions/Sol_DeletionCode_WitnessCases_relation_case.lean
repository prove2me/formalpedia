-- Prove2me | solution 1 for DeletionCode.WitnessCases.relation_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:44:52.139383+00:00
-- url     : https://prove2.me/submissions/c293ed35-abb2-407c-b42f-9a4780b3c184

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
import Definitions.Def_DeletionCode_WitnessCases
import Theorems.Thm_DeletionCode_WitnessCases_relation_hull_card
import Theorems.Thm_DeletionCode_FiniteGenerating_generating_blockHull
import Theorems.Thm_DeletionCode_GeneratingBlocks_generating_blockHull
import Theorems.Thm_DeletionCode_GeneratingBlocks_subset_blockHull
import Theorems.Thm_DeletionCode_RelationBlockSavings_blockHull_subset
import Theorems.Thm_DeletionCode_RelationBlockSavings_relation_block_hull_bound
import Theorems.Thm_DeletionCode_RelationBlockSavings_subset_blockHull


set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCases
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition FiniteGenerating FiniteRelationBlocks CatalogueAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessCases
theorem _root_.solution {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G I : RuleSet k) (hIG : I ⊆ G) (hI : 2 ≤ I.card)
    (hgen : GeneratingAt v G) (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (hK : ∀ u ∈ G, u ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    Witness t k v K (RelationBlockSavings.blockHull G I) := by
  let U := RelationBlockSavings.blockHull G I
  have hUG : U ⊆ G := RelationBlockSavings.blockHull_subset G I
  have hlow : 2 ≤ U.card := hI.trans
    (Finset.card_le_card (RelationBlockSavings.subset_blockHull G I hIG))
  have hupper : U.card ≤ 2 * t * windowLength k :=
    relation_hull_card G I hIG w hw a hgen.independent ha hrel hsize
  have hc : componentCount U ≤ (2 * t - 1) * U.card :=
    RelationBlockSavings.relation_block_hull_bound ht G I hIG hI hcat w hw a ha hrel
  have hL : 1 ≤ windowLength k := by unfold windowLength; omega
  have hquad : 2 * t * windowLength k ≤ 1 + 4 * t * (windowLength k) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (2 * t * windowLength k) hL]
  exact ⟨generating_blockHull hgen I, (fun u hu => hcat u (hUG hu)),
    (fun u hu => hK u (hUG hu)), hlow, hupper.trans hquad, hc.trans (Nat.le_succ _), fun _ => hc⟩
end DeletionCode.WitnessCases
