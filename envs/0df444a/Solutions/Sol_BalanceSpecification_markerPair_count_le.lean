-- Prove2me | solution 1 for BalanceSpecification.markerPair_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:22.202129+00:00
-- url     : https://prove2.me/submissions/559aa49c-4537-4791-be95-42fda889697e

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Theorems.Thm_BalanceSpecification_reverse_idxOf_last_marker
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hs : IsSynchronizing (language X) [none])
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X) (n : ℕ) :
    (∑ k : Fin n, (predecessorFinset (language X) [none] (k.val + 1)).card *
      wordCount (language Y) (n - 1 - k.val)) ≤ wordCount (language X) (n + 1) := by
  classical
  have hcard : (markerPairFinset X Y n).card =
      ∑ k : Fin n, (predecessorFinset (language X) [none] (k.val + 1)).card *
        wordCount (language Y) (n - 1 - k.val) := by
    rw [markerPairFinset, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro k _
    exact Finset.card_product ..
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun z : (_k : Fin n) × (Word (Option A) × Word A) =>
      z.2.1 ++ [none] ++ z.2.2.map some)
  · intro z hz
    obtain ⟨_, hpair⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hp, hv⟩ := Finset.mem_product.mp hpair
    obtain ⟨hpL, hplen, hpmark⟩ := mem_predecessorFinset.mp hp
    obtain ⟨hvL, hvlen⟩ := mem_wordFinset.mp hv
    apply mem_wordFinset.mpr
    constructor
    · exact hs.2 z.2.1 (z.2.2.map some) hpmark (hext _ hvL)
    · simp only [List.length_append, List.length_singleton, List.length_map, hplen, hvlen]
      have := z.1.isLt
      omega
  · intro z hz t ht heq
    obtain ⟨_, hpair⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hp, hv⟩ := Finset.mem_product.mp hpair
    obtain ⟨_, hpair'⟩ := Finset.mem_sigma.mp ht
    obtain ⟨hq, hw⟩ := Finset.mem_product.mp hpair'
    have hplen := (mem_predecessorFinset.mp hp).2.1
    have hqlen := (mem_predecessorFinset.mp hq).2.1
    have hvlen := (mem_wordFinset.mp hv).2
    have hwlen := (mem_wordFinset.mp hw).2
    have hlast := congrArg (fun z : Word (Option A) => z.reverse.idxOf none) heq
    rw [reverse_idxOf_last_marker, reverse_idxOf_last_marker, hvlen, hwlen] at hlast
    have hki : z.1 = t.1 := Fin.ext (by have := z.1.isLt; have := t.1.isLt; omega)
    cases z with
    | mk k ps =>
      cases t with
      | mk l qt =>
        change k = l at hki
        subst l
        have hpq : ps.1 = qt.1 := List.append_inj_left
          (by simpa only [List.append_assoc] using heq) (hplen.trans hqlen.symm)
        have hsuffix : [none] ++ ps.2.map some = [none] ++ qt.2.map some :=
          List.append_inj_right (by simpa only [List.append_assoc] using heq)
            (hplen.trans hqlen.symm)
        have hmap := (List.cons.inj hsuffix).2
        have hvw : ps.2 = qt.2 := (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp hmap
        exact Sigma.ext rfl (heq_of_eq (Prod.ext hpq hvw))
end BalanceSpecification
