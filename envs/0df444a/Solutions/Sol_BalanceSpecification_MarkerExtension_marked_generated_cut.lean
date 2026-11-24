-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marked_generated_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:53.959226+00:00
-- url     : https://prove2.me/submissions/0fc9df1b-6966-4702-9e34-d2c82d3e2840

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_none_not_mem_map_some
public import Theorems.Thm_BalanceSpecification_MarkerExtension_markerFree_prefix_split
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
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
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {P : Set (Word A)} {z p q : Word (Option A)}
    (hz : z ∈ generatedWords (markedCode P)) (heq : z = p ++ none :: q) :
    p ∈ generatedWords (markedCode P) ∧ none :: q ∈ generatedWords (markedCode P) := by
  obtain ⟨ws, hws, rfl⟩ := hz
  have aux : ∀ ws : List (Word (Option A)),
      (∀ g ∈ ws, g ∈ markedCode P) → ∀ p q,
      ws.flatten = p ++ none :: q →
      p ∈ generatedWords (markedCode P) ∧ none :: q ∈ generatedWords (markedCode P) := by
    intro ws
    induction ws with
    | nil =>
      intro _ p q h
      have H := congrArg List.length h
      simp only [List.flatten_nil, List.length_nil, List.length_append, List.length_cons] at H
      omega
    | cons g ws ih =>
      intro hall p q h
      have hg : g ∈ markedCode P := hall g List.mem_cons_self
      obtain ⟨v, hv, rfl⟩ := hg
      have htail : ∀ z ∈ ws, z ∈ markedCode P :=
        fun z hz => hall z (List.mem_cons_of_mem _ hz)
      cases p with
      | nil =>
        exact ⟨nil_mem_generatedWords _, ⟨_, hall, h⟩⟩
      | cons a p =>
        have hs : v.map some ++ ws.flatten = p ++ none :: q :=
          (List.cons.inj h).2
        have ha : (none : Option A) = a := (List.cons.inj h).1
        obtain ⟨r, hr, hrest⟩ := markerFree_prefix_split (none_not_mem_map_some v) hs
        obtain ⟨hpre, hsuf⟩ := ih htail r q hrest
        refine ⟨?_, hsuf⟩
        have hhead : none :: v.map some ∈ generatedWords (markedCode P) :=
          mem_generatedWords_of_mem ⟨v, hv, rfl⟩
        simpa only [hr, List.cons_append, ha] using append_mem_generatedWords hhead hpre
  exact aux ws hws p q heq
end BalanceSpecification.MarkerExtension
