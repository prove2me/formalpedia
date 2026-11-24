-- Prove2me | solution 1 for BalanceSpecification.hasVariableSpecification_of_entropyMinimal_synchronized_biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:28.981079+00:00
-- url     : https://prove2.me/submissions/080ccd70-ab18-4428-84a4-b92fe3e18526

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Theorems.Thm_BalanceSpecification_uniform_occurrences_of_entropyMinimal_biBalanced
public import Theorems.Thm_BalanceSpecification_hasVariableSpecification_of_bounded_synchronizing_occurrences
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution
    {X : ShiftSpace A} (hEM : EntropyMinimal X) (hS : Synchronized X)
    (hB : BiBalanced (language X)) : HasVariableSpecification X := by
  obtain ⟨v, hv⟩ := hS.2
  obtain ⟨N, _, hocc⟩ := uniform_occurrences_of_entropyMinimal_biBalanced hEM hB v hv.1
  apply hasVariableSpecification_of_bounded_synchronizing_occurrences hv (N := N)
  · intro u hu
    obtain ⟨s, hs, hvs⟩ := (hocc u hu).1
    obtain ⟨_, hslen, hus⟩ := mem_followerFinset.mp hs
    exact ⟨s, hslen.le, hus, hvs⟩
  · intro u hu
    obtain ⟨p, hp, hvp⟩ := (hocc u hu).2
    obtain ⟨_, hplen, hpu⟩ := mem_predecessorFinset.mp hp
    exact ⟨p, hplen.le, hpu, hvp⟩
end BalanceSpecification
