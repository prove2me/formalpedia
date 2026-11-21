-- Prove2me | solution 1 for Cage87.mem_branch_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:26.135384+00:00
-- url     : https://prove2.me/submissions/024b4d62-5f67-4f35-b2d4-3547a87405e8

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_beq_false_of_ne
public import Theorems.Thm_Cage87_G_adj
attribute [local simp] Cage87.G_adj

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution {v x y z : Nat} (hy : y ∈ nb adj x) (hyv : y ≠ v) (hz : z ∈ nb adj y)
    (hzx : z ≠ x) : z ∈ branch adj v x := by
  simp only [branch, List.mem_cons, List.mem_append, List.mem_filter, List.mem_flatMap,
    Bool.not_eq_true']
  exact Or.inr (Or.inr ⟨y, ⟨hy, beq_false_of_ne hyv⟩, hz, beq_false_of_ne hzx⟩)
end Cage87
