-- Prove2me | solution 1 for BalanceSpecification.wordCount_productShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:33.056994+00:00
-- url     : https://prove2.me/submissions/dfddb8db-23e8-440b-bb68-c452959efc2b

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_word_eq_of_projection_maps
public import Theorems.Thm_BalanceSpecification_mem_language_productShift_iff
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution [Fintype A] [Fintype B]
    [TopologicalSpace A] [TopologicalSpace B] (X : ShiftSpace A) (Y : ShiftSpace B) (n : ℕ) :
    wordCount (language (productShift X Y)) n =
      wordCount (language X) n * wordCount (language Y) n := by
  classical
  unfold wordCount
  rw [← Finset.card_product]
  apply Finset.card_bij (fun w _ => (w.map Prod.fst, w.map Prod.snd))
  · intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    obtain ⟨h1, h2⟩ := mem_language_productShift_iff.mp hwL
    exact Finset.mem_product.mpr ⟨mem_wordFinset.mpr ⟨h1, by simpa only [List.length_map] using hwlen⟩,
      mem_wordFinset.mpr ⟨h2, by simpa only [List.length_map] using hwlen⟩⟩
  · intro w hw v hv heq
    exact word_eq_of_projection_maps (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    obtain ⟨hu, hulen⟩ := mem_wordFinset.mp h1
    obtain ⟨hv, hvlen⟩ := mem_wordFinset.mp h2
    have hfst : (p.1.zip p.2).map Prod.fst = p.1 := List.map_fst_zip (by omega)
    have hsnd : (p.1.zip p.2).map Prod.snd = p.2 := List.map_snd_zip (by omega)
    refine ⟨p.1.zip p.2, mem_wordFinset.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_language_productShift_iff.mpr
        ⟨by rw [hfst]; exact hu, by rw [hsnd]; exact hv⟩
    · simp only [List.length_zip, hulen, hvlen, min_self]
    · exact Prod.ext hfst hsnd
end BalanceSpecification
