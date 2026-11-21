-- Prove2me | solution 1 for Cage87.branch_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:36.963087+00:00
-- url     : https://prove2.me/submissions/75d03c6a-deef-451e-805a-3b3c49f732dc

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge
public import Theorems.Thm_Cage87_G_adj
public import Theorems.Thm_Cage87_testBit_maskOf
public import Theorems.Thm_Cage87_pairwise_of_pwDisj
public import Theorems.Thm_Cage87_pairwise_rel
public import Theorems.Thm_Cage87_vertices_ok

attribute [local simp] Cage87.G_adj

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution {v x y z : Nat} (hv : v < 768) (hx : x ∈ nb adj v) (hy : y ∈ nb adj v)
    (hxy : x ≠ y) (hzx : z ∈ branch adj v x) (hzy : z ∈ branch adj v y) : False := by
  have hp := pairwise_of_pwDisj _ (vertices_ok v hv)
  rw [List.pairwise_map] at hp
  have key : ∀ a b, brMask adj v a &&& brMask adj v b = 0 → z ∈ branch adj v a →
      z ∈ branch adj v b → False := by
    intro a b hab ha hb
    have h1 := (testBit_maskOf z _).mpr ha
    have h2 := (testBit_maskOf z _).mpr hb
    have : (brMask adj v a &&& brMask adj v b).testBit z = true := by
      rw [Nat.testBit_and]; simp only [brMask] at h1 h2 ⊢; rw [h1, h2]; rfl
    rw [hab] at this
    simp at this
  rcases pairwise_rel hp hx hy hxy with h | h
  · exact key x y h hzx hzy
  · exact key y x h hzy hzx
end Cage87
