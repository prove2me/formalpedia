-- Prove2me | solution 1 for BalanceSpecification.uniform_occurrences_of_entropyMinimal_biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:34.050473+00:00
-- url     : https://prove2.me/submissions/d0e40b74-d1cc-43da-84ae-704d82d3cf50

module
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Definitions.Def_BalanceSpecificaton_Occurrence
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Theorems.Thm_BalanceSpecification_avoidance_ratio_tendsto_zero_of_entropyMinimal
public import Theorems.Thm_BalanceSpecification_exists_uniform_occurrences_of_avoidance_ratio_tendsto_zero


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A}
    (hEM : EntropyMinimal X) (hB : BiBalanced (language X))
    (v : Word A) (hv : v ∈ language X) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ language X,
      (∃ s ∈ followerFinset (language X) u N, v <:+: s) ∧
      (∃ p ∈ predecessorFinset (language X) u N, v <:+: p) :=
  exists_uniform_occurrences_of_avoidance_ratio_tendsto_zero hB v
    (avoidance_ratio_tendsto_zero_of_entropyMinimal hEM hv)
end BalanceSpecification
