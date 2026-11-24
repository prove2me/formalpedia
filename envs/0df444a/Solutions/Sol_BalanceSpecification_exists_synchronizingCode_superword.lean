-- Prove2me | solution 1 for BalanceSpecification.exists_synchronizingCode_superword
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:10.463854+00:00
-- url     : https://prove2.me/submissions/003d7121-6c6a-4378-8279-6ef67ea0a3cc

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SynchronizedCoded
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : ShiftSpace A}
omit [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {v : Word A}
    (hirr : Irreducible X) (hv : IsSynchronizing (language X) v)
    {u : Word A} (hu : u ∈ language X) :
    ∃ w ∈ synchronizingCode X v, u <:+: w := by
  obtain ⟨x, hx, _, _⟩ := hv.1
  let p := block x 0 1
  have hp : p ∈ language X := block_mem_language hx _ _
  have hplen : p.length = 1 := length_block _ _ _
  obtain ⟨γ, _, ht⟩ := hirr u hu p hp
  obtain ⟨α, _, hvt⟩ := hirr v hv.1 (u ++ γ ++ p) ht
  obtain ⟨β, _, hwhole⟩ := hirr (v ++ α ++ (u ++ γ ++ p)) hvt v hv.1
  let w := v ++ α ++ (u ++ γ ++ p) ++ β
  refine ⟨w, ⟨?_, α ++ (u ++ γ ++ p) ++ β, ?_, hwhole⟩, ?_⟩
  · intro heq
    have hzero := congrArg List.length heq
    simp only [w, List.length_append, hplen, List.length_nil] at hzero
    omega
  · simp only [w, List.append_assoc]
  · refine ⟨v ++ α, γ ++ p ++ β, ?_⟩
    simp only [w, List.append_assoc]
end BalanceSpecification
