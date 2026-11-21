-- Prove2me | solution 1 for Cage87.pairwise_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:27:01.880891+00:00
-- url     : https://prove2.me/submissions/ab50b13e-e886-479c-b1d5-339fb2de6aee

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
theorem _root_.solution {α : Type*} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hxy
    · exact Or.inl (h.1 y hy')
    · exact Or.inr (h.1 x hx')
    · exact solution h.2 hx' hy' hxy
end Cage87
