-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.relation_seeded_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:29.722396+00:00
-- url     : https://prove2.me/submissions/b89560ab-4437-46fc-a375-cb62c9cd71a1

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_RelationBlockSavings_seeded_component_growth
import Theorems.Thm_DeletionCode_RelationSavings_savings_from_relation


set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {t k : ℕ} (ht : 2 ≤ t) (U I : RuleSet k)
    (hIU : I ⊆ U) (hI : 2 ≤ I.card) (hcat : ∀ u ∈ U, CatalogueRule t k u)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount U ≤ (2 * t - 1) * U.card := by
  have hsave := RelationSavings.savings_from_relation I
    (fun u hu => hcat u (hIU hu)) w hw a ha hrel
  have hprod := Nat.mul_le_mul_left (t - 1) hI
  have hcoef : 2 * t - 1 = t + (t - 1) := by omega
  have hsmall : t * I.card + t ≤ (2 * t - 1) * I.card := by
    rw [hcoef, Nat.add_mul]
    omega
  have hseed : componentCount I ≤ (2 * t - 1) * I.card := hsave.trans hsmall
  have hgrowth := seeded_component_growth (by omega : 1 ≤ t) U I hIU hcat hcover
  have hcard := Finset.card_le_card hIU
  have hadd : I.card + (U.card - I.card) = U.card := by omega
  calc
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := hgrowth
    _ ≤ (2 * t - 1) * I.card + (2 * t - 1) * (U.card - I.card) :=
      Nat.add_le_add_right hseed _
    _ = (2 * t - 1) * U.card := by rw [← Nat.mul_add, hadd]
end DeletionCode.RelationBlockSavings
