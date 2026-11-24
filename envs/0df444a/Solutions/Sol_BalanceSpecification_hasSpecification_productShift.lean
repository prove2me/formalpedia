-- Prove2me | solution 1 for BalanceSpecification.hasSpecification_productShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:09.769364+00:00
-- url     : https://prove2.me/submissions/9060a532-ad3a-4a41-85ed-f08a8f1ef430

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_mem_language_productShift_iff
public import Theorems.Thm_BalanceSpecification_specification_bridge_of_le
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
theorem _root_.solution [TopologicalSpace A] [TopologicalSpace B]
    {X : ShiftSpace A} {Y : ShiftSpace B} (hX : HasSpecification X) (hY : HasSpecification Y) :
    HasSpecification (productShift X Y) := by
  obtain ⟨N, hN⟩ := hX
  obtain ⟨M, hM⟩ := hY
  refine ⟨max N M, ?_⟩
  intro u hu v hv
  obtain ⟨hu1, hu2⟩ := mem_language_productShift_iff.mp hu
  obtain ⟨hv1, hv2⟩ := mem_language_productShift_iff.mp hv
  obtain ⟨a, ha, halen, huxa⟩ := specification_bridge_of_le hN (le_max_left N M) _ hu1 _ hv1
  obtain ⟨b, hb, hblen, huyb⟩ := specification_bridge_of_le hM (le_max_right N M) _ hu2 _ hv2
  have hfst : (a.zip b).map Prod.fst = a := List.map_fst_zip (by omega)
  have hsnd : (a.zip b).map Prod.snd = b := List.map_snd_zip (by omega)
  refine ⟨a.zip b, mem_language_productShift_iff.mpr
    ⟨by rw [hfst]; exact ha, by rw [hsnd]; exact hb⟩, ?_, ?_⟩
  · simp only [List.length_zip, halen, hblen, min_self]
  · apply mem_language_productShift_iff.mpr
    simp only [List.map_append, hfst, hsnd]
    exact ⟨huxa, huyb⟩
end BalanceSpecification
