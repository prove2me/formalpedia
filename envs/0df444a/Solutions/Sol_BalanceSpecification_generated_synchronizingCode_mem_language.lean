-- Prove2me | solution 1 for BalanceSpecification.generated_synchronizingCode_mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:09.57259+00:00
-- url     : https://prove2.me/submissions/f82c3ccb-20c8-4749-b402-7faaec3dd886

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SynchronizedCoded
public import Theorems.Thm_BalanceSpecification_IsFactorial_prefix
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
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
    (hv : IsSynchronizing (language X) v) :
    generatedWords (synchronizingCode X v) ⊆ language X := by
  have hlist : ∀ ws : List (Word A),
      (∀ w ∈ ws, w ∈ synchronizingCode X v) →
      ∀ z : Word A, z ++ v ∈ language X → (z ++ ws.flatten) ++ v ∈ language X := by
    intro ws
    induction ws with
    | nil => intro _ z hz; simpa only [List.flatten_nil, List.append_nil] using hz
    | cons w ws ih =>
      intro hws z hz
      obtain ⟨_, t, hwt, hreturn⟩ := hws w (List.mem_cons_self ..)
      have hnext : (z ++ w) ++ v ∈ language X := by
        have hright : v ++ (t ++ v) ∈ language X := by
          simpa only [hwt, List.append_assoc] using hreturn
        simpa only [hwt, List.append_assoc] using hv.2 z (t ++ v) hz hright
      have htail := ih (fun q hq => hws q (List.mem_cons_of_mem w hq)) (z ++ w) hnext
      simpa only [List.flatten_cons, List.append_assoc] using htail
  rintro w ⟨ws, hws, rfl⟩
  have h := hlist ws hws [] (by simpa only [List.nil_append] using hv.1)
  exact (language_factorial X).prefix (by simpa only [List.nil_append] using h)
end BalanceSpecification
