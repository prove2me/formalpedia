-- Prove2me | solution 1 for BalanceSpecification.avoiding_shift_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:40:54.30672+00:00
-- url     : https://prove2.me/submissions/1d264abf-9a19-42cc-8ebf-7b3c2be54061

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
public import Theorems.Thm_BalanceSpecification_mem_carrier_iff_blocks
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_avoidingLanguage
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_languageShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} {v : Word A}
    (hv : v ∈ language X) :
    (languageShift (avoidingLanguage (language X) v)).carrier ⊂ X.carrier := by
  have hsub : (languageShift (avoidingLanguage (language X) v)).carrier ⊆ X.carrier := by
    intro x hx
    apply mem_carrier_iff_blocks.mpr
    intro k n
    exact (mem_languageShift_iff.mp hx k n).1
  obtain ⟨x, hx, k, hvblock⟩ := hv
  have hnot : x ∉ (languageShift (avoidingLanguage (language X) v)).carrier := by
    intro hxcore
    have havoid := (mem_languageShift_iff.mp hxcore k v.length).2
    rw [hvblock] at havoid
    exact havoid ⟨[], [], by simp only [List.nil_append, List.append_nil]⟩
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  exact hnot (heq.symm ▸ hx)
end BalanceSpecification
