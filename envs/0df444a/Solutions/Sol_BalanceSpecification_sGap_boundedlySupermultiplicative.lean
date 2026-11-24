-- Prove2me | solution 1 for BalanceSpecification.sGap_boundedlySupermultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:42.159373+00:00
-- url     : https://prove2.me/submissions/417a5e9e-e3e0-490b-a445-1c8922132733

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBSM
public import Theorems.Thm_BalanceSpecification_exists_sGap_pressure_base
public import Theorems.Thm_BalanceSpecification_sGap_boundedlySupermultiplicative_of_pressure
public import Theorems.Thm_BalanceSpecification_biBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_hasBoundedSuccessiveGaps_of_finite
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
public import Theorems.Thm_BalanceSpecification_sGap_hasVariableSpecification_of_bounded_gaps


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty) :
    BoundedlySupermultiplicative (language (sGapShift S)) := by
  classical
  by_cases hfinite : S.Finite
  · have hspec := sGap_hasVariableSpecification_of_bounded_gaps hS
      (hasBoundedSuccessiveGaps_of_finite hfinite)
    exact boundedlySupermultiplicative_of_rightBalanced (language_factorial (sGapShift S))
      (biBalanced_of_hasVariableSpecification (sGapShift_nonempty hS) hspec).1
  · obtain ⟨a, ha⟩ := hS
    obtain ⟨b, hb, hba⟩ := (show S.Infinite from hfinite).exists_notMem_finset {a}
    have hab : a ≠ b := by
      intro h
      exact hba (Finset.mem_singleton.mpr h.symm)
    obtain ⟨β, hβ, hroot⟩ := exists_sGap_pressure_base ha hb hab
    exact sGap_boundedlySupermultiplicative_of_pressure ⟨a, ha⟩ hβ hroot
end BalanceSpecification
