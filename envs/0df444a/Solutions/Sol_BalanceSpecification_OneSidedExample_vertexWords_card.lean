-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.vertexWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:37.663808+00:00
-- url     : https://prove2.me/submissions/0520f4e1-1515-4994-91f4-eb55302d706e

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_OneSidedExample_runWord_injective
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.OneSidedExample.length_runWord
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
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
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (s : Vertex) (n : ℕ) : (vertexWords s n).card = 2 ^ n := by
  classical
  unfold vertexWords
  rw [Finset.card_image_of_injective _ (runWord_injective s)]
  have heq : allWords (A := Bool) n =
      Finset.univ.image (fun f : Fin n → Bool => List.ofFn f) := by
    ext w
    constructor
    · intro hw
      have hlen := mem_allWords.mp hw
      subst n
      exact Finset.mem_image.mpr ⟨fun i => w[i.val], Finset.mem_univ _, List.ofFn_getElem⟩
    · intro hw
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hw
      exact mem_allWords.mpr List.length_ofFn
  rw [heq]
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
end BalanceSpecification.OneSidedExample
