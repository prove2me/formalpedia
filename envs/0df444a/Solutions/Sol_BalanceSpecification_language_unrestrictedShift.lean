-- Prove2me | solution 1 for BalanceSpecification.language_unrestrictedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:42.229679+00:00
-- url     : https://prove2.me/submissions/fb54e680-12ab-4699-b6bf-c1058980e195

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
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
theorem _root_.solution [TopologicalSpace A] [Nonempty A] :
    language (unrestrictedShift A) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro w
  obtain ⟨a⟩ := ‹Nonempty A›
  let x : Configuration A := fun i => w[i.toNat]?.getD a
  refine ⟨x, Set.mem_univ _, 0, ?_⟩
  apply List.ext_getElem
  · exact length_block _ _ _
  · intro i hi hi'
    simp only [block, List.getElem_ofFn, x, zero_add, Int.toNat_natCast,
      List.getElem?_eq_getElem hi', Option.getD_some]
end BalanceSpecification
