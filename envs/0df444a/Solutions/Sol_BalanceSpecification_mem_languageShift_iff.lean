-- Prove2me | solution 1 for BalanceSpecification.mem_languageShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:28.317868+00:00
-- url     : https://prove2.me/submissions/eaf219d5-1f4b-46e3-a16e-bb6dbf512cdb

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} {x : Configuration A} :
    x ∈ (languageShift L).carrier ↔ ∀ k n, block x k n ∈ L := by
  constructor
  · intro hx k n
    by_contra hn
    exact hx (block x k n) hn k (by rw [length_block])
  · intro hx w hw k heq
    have hmem := hx k w.length
    rw [heq] at hmem
    exact hw hmem
end BalanceSpecification
