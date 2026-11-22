-- Prove2me | solution 1 for CircuitComplexity.Valiant.depth_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:08.322806+00:00
-- url     : https://prove2.me/submissions/8a0515e2-59d8-4027-84be-c3b1cddf2e47

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_CircuitComplexity_Valiant
public import Theorems.Thm_CircuitComplexity_Valiant_depth_deleteEdges_levelEdges_le
public import Theorems.Thm_CircuitComplexity_Valiant_exists_r_levels_small
public import Theorems.Thm_Digraph_deleteEdges_empty_depth


set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
namespace CircuitComplexity.Valiant
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) [DecidableRel G.Adj]
    {k r : Nat} (hrk : r ≤ k)
    (hd : G.depth ≤ 2 ^ k) :
    ∃ F : Finset (V × V),
      F ⊆ G.edgeFinset ∧
      k * F.card ≤ r * G.edgeFinset.card ∧
      (G.deleteEdges F).depth ≤ 2 ^ k / 2 ^ r := by
  by_cases hac : IsAcyclic G
  · obtain ⟨I, hIsub, hIcard, hIsum⟩ := exists_r_levels_small G hrk hac hd
    refine ⟨I.biUnion fun i => levelEdges G k i, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨i, _, hie⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hie).1
    · calc k * (I.biUnion fun i => levelEdges G k i).card
          ≤ k * ∑ i ∈ I, (levelEdges G k i).card := Nat.mul_le_mul_left k Finset.card_biUnion_le
        _ ≤ r * G.edgeFinset.card := hIsum
    · have hbound := depth_deleteEdges_levelEdges_le G hac hd I hIsub
      rw [hIcard] at hbound
      have hpow : (2 : ℕ) ^ k / 2 ^ r = 2 ^ (k - r) := Nat.pow_div hrk (by decide)
      simp_all
  · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    rw [deleteEdges_empty_depth]
    change sSup _ ≤ _
    rw [Nat.sSup_of_not_bddAbove hac]
    exact Nat.zero_le _
end CircuitComplexity.Valiant
