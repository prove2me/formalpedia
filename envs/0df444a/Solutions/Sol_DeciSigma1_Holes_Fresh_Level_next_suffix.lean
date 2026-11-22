-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.next_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:16.057391+00:00
-- url     : https://prove2.me/submissions/2676ef9c-f2e0-411e-b0d5-2ebacb78343b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_of_suffix_of_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_start_lt
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
namespace DeciSigma1.Holes.Fresh.Level
theorem _root_.solution (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    L.marker l <:+ (L.next W).marker l ∧ (L.marker l).length < ((L.next W).marker l).length := by
  have hns := next_start_lt hA hS hl
  have hσl := (hS l (next_active_subset W hl)).length_le
  have hlen : (L.marker l).length < ((L.next W).marker l).length := by
    simp only [next, List.length_drop]; omega
  exact
      ⟨suffix_of_suffix_of_le (hS l (next_active_subset W hl)) (List.drop_suffix _ _) hlen.le, hlen⟩
end DeciSigma1.Holes.Fresh.Level
