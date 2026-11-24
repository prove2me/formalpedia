-- Prove2me | solution 1 for BalanceSpecification.mem_language_productShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:01.862948+00:00
-- url     : https://prove2.me/submissions/59fbf58b-184e-47ed-b1eb-ca44a434161b

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_block_map
public import Theorems.Thm_BalanceSpecification_word_eq_of_projection_maps
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
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
    {X : ShiftSpace A} {Y : ShiftSpace B} {w : Word (A × B)} :
    w ∈ language (productShift X Y) ↔
      w.map Prod.fst ∈ language X ∧ w.map Prod.snd ∈ language Y := by
  constructor
  · rintro ⟨z, hz, k, hk⟩
    constructor
    · refine ⟨fun i => (z i).1, hz.1, k, ?_⟩
      simpa only [List.length_map, block_map] using congrArg (List.map Prod.fst) hk
    · refine ⟨fun i => (z i).2, hz.2, k, ?_⟩
      simpa only [List.length_map, block_map] using congrArg (List.map Prod.snd) hk
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx, hxb⟩ := mem_language_iff_exists_block_zero.mp h1
    obtain ⟨y, hy, hyb⟩ := mem_language_iff_exists_block_zero.mp h2
    simp only [List.length_map] at hxb hyb
    refine ⟨fun i => (x i, y i), ⟨hx, hy⟩, 0, ?_⟩
    apply word_eq_of_projection_maps
    · simpa only [block_map] using hxb
    · simpa only [block_map] using hyb
end BalanceSpecification
