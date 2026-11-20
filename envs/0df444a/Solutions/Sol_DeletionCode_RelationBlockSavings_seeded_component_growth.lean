-- Prove2me | solution 1 for DeletionCode.RelationBlockSavings.seeded_component_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:30.152185+00:00
-- url     : https://prove2.me/submissions/0be3a297-42ef-468d-a3d8-2567aabf005c

import Definitions.Def_DeletionCode_RelationSavings
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_RelationBlockSavings
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_ConnectedBlocks_adjoining_rule_bound
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


section
namespace DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
private theorem seeded_frontier {k : ℕ} (U I S : RuleSet k)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u)
    (hIS : I ⊆ S) (hSU : S ⊆ U) (hne : S ≠ U) :
    ∃ w ∈ U, w ∉ S ∧ ∃ u ∈ S, RuleAdjacent w u ∨ RuleAdjacent u w := by
  classical
  by_contra hnone
  have preserve : ∀ a b,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) a b →
      (a ∈ S ↔ b ∈ S) := by
    intro a b hpath
    induction hpath with
    | rel a b hedge =>
      obtain ⟨haU, hbU, hr⟩ := hedge
      constructor
      · intro haS
        by_contra hbS
        exact hnone ⟨b, hbU, hbS, a, haS, Or.inr hr⟩
      · intro hbS
        by_contra haS
        exact hnone ⟨a, haU, haS, b, hbS, Or.inl hr⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  have hUS : U ⊆ S := by
    intro u hu
    obtain ⟨i, hi, hpath⟩ := hcover u hu
    exact (preserve i u hpath).mp (hIS hi)
  exact hne (Finset.Subset.antisymm hSU hUS)
end DeletionCode.RelationBlockSavings
end

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSavings
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSavings
theorem _root_.solution {t k : ℕ} (ht : 1 ≤ t) (U I : RuleSet k)
    (hIU : I ⊆ U) (hcat : ∀ w ∈ U, CatalogueRule t k w)
    (hcover : ∀ u ∈ U, ∃ i ∈ I,
      Relation.EqvGen (FiniteConnectedGrowth.Induced U RuleAdjacent) i u) :
    componentCount U ≤ componentCount I + (2 * t - 1) * (U.card - I.card) := by
  classical
  let d := 2 * t - 1
  let P : RuleSet k → Prop := fun S =>
    componentCount S + d * I.card ≤ componentCount I + d * S.card
  have aux : ∀ n : ℕ, ∀ S : RuleSet k, I ⊆ S → S ⊆ U → P S →
      U.card - S.card = n → P U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hIS hSU hP hdiff
      by_cases heq : S = U
      · simpa only [heq] using hP
      · obtain ⟨w, hwU, hwS, hadj⟩ := seeded_frontier U I S hcover hIS hSU heq
        have hSU' : insert w S ⊆ U := Finset.insert_subset_iff.mpr ⟨hwU, hSU⟩
        have hIS' : I ⊆ insert w S := hIS.trans (Finset.subset_insert w S)
        have hstep : componentCount (insert w S) ≤ componentCount S + d := by
          apply adjoining_rule_bound ht S w (hcat w hwU)
          obtain ⟨u, hu, hwu | huw⟩ := hadj
          · exact ⟨u, hu, hwu⟩
          · exact ⟨u, hu, huw.symm⟩
        have hcard : (insert w S).card = S.card + 1 := Finset.card_insert_of_notMem hwS
        have hP' : P (insert w S) := by
          change componentCount (insert w S) + d * I.card ≤
            componentCount I + d * (insert w S).card
          change componentCount S + d * I.card ≤ componentCount I + d * S.card at hP
          rw [hcard, Nat.mul_add, Nat.mul_one]
          omega
        have hbound : (insert w S).card ≤ U.card := Finset.card_le_card hSU'
        have hsmaller : U.card - (insert w S).card < n := by omega
        exact ih (U.card - (insert w S).card) hsmaller (insert w S)
          hIS' hSU' hP' rfl
  have hfinal := aux (U.card - I.card) I (by intro u hu; exact hu) hIU
    (by dsimp [P]; exact le_rfl) rfl
  change componentCount U + d * I.card ≤ componentCount I + d * U.card at hfinal
  have hcard := Finset.card_le_card hIU
  have hadd : I.card + (U.card - I.card) = U.card := by omega
  have hmul : d * U.card = d * I.card + d * (U.card - I.card) := by
    rw [← Nat.mul_add, hadd]
  rw [hmul] at hfinal
  change componentCount U ≤ componentCount I + d * (U.card - I.card)
  omega
end DeletionCode.RelationBlockSavings
