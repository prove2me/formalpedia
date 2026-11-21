-- Prove2me | solution 1 for Cage87.testBit_maskOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:26:51.121404+00:00
-- url     : https://prove2.me/submissions/ffc9c10e-61aa-468a-991e-9346e34605a0

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
attribute [local simp] Cage87.G_adj

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution (z : Nat) : ∀ l : List Nat, (maskOf l).testBit z = true ↔ z ∈ l
  | [] => by simp [maskOf]
  | x :: l => by
    simp only [maskOf]
    show (1 <<< x ||| maskOf l).testBit z = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, solution z l, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.mem_cons, decide_eq_true_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
end Cage87
