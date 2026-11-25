-- Prove2me | solution 1 for ErdosPosa.IsMax023.adj_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:02.210234+00:00
-- url     : https://prove2.me/submissions/608bf1ee-006c-4132-bf0d-d904606d7692

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Theorems.Thm_ErdosPosa_IsMax023_no_path_W
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
namespace IsMax023
theorem _root_.solution (hH : IsMax023 G H) {w1 w2 : V} (hw1 : deg H w1 = 2)
    (hw2 : deg H w2 = 2) (hG : G.Adj w1 w2) : H.Adj w1 w2 := by
  by_contra hn
  refine hH.no_path_W hw1 hw2 hG.ne (Walk.cons hG Walk.nil) ?_ ?_
  · intro x hx
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro e he
    simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact hn
end IsMax023
end ErdosPosa
