-- Prove2me | solution 1 for Cage87.nodup_of_nodupB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:26:47.753348+00:00
-- url     : https://prove2.me/submissions/7245c84b-4464-4aae-97c7-8cee0a3bc1ff

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Cage87_Bridge

set_option autoImplicit true
@[expose] public section
public section
open Cage87
open SimpleGraph
namespace Cage87
theorem _root_.solution : ∀ l : List Nat, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hx => ?_, solution l h.2⟩
    have := List.contains_iff_mem.mpr hx
    rw [h.1] at this
    exact Bool.false_ne_true this
end Cage87
