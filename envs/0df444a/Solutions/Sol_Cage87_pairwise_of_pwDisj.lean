-- Prove2me | solution 1 for Cage87.pairwise_of_pwDisj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:26:52.855214+00:00
-- url     : https://prove2.me/submissions/43edc258-cdd4-44aa-846e-dcd7facf19e1

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
theorem _root_.solution : ∀ ms : List Nat, pwDisj ms = true → ms.Pairwise (fun a b => a &&& b = 0)
  | [], _ => List.Pairwise.nil
  | m :: ms, h => by
    simp only [pwDisj, Bool.and_eq_true, List.all_eq_true, Nat.beq_eq] at h
    exact List.Pairwise.cons (fun m' hm' => h.1 m' hm') (solution ms h.2)
end Cage87
