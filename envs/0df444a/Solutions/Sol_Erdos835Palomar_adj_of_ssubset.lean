-- Prove2me | solution 1 for Erdos835Palomar.adj_of_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:17.153695+00:00
-- url     : https://prove2.me/submissions/c227cd0f-baeb-47fb-8855-2d5cd08e6729

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
variable {α : Type*} [DecidableEq α]
variable {k : ℕ}
namespace Erdos835Palomar
theorem _root_.solution {A : Finset (Fin (2 * k))} (hA : #A = k + 1)
    {s t : {s : Finset (Fin (2 * k)) // #s = k}} (hs : s.val ⊂ A) (ht : t.val ⊂ A)
    (hst : s ≠ t) : J(2 * k, k).Adj s t := by
  rw [johnson_adj]
  have hU : #(s.val ∪ t.val) = k + 1 := by
    apply le_antisymm
    · rw [← hA]; exact card_le_card (union_subset hs.subset ht.subset)
    · have hne : s.val ≠ t.val := fun h => hst (Subtype.ext h)
      have hlt : #s.val < #(s.val ∪ t.val) := by
        apply card_lt_card
        refine ssubset_of_subset_of_ne subset_union_left ?_
        intro h
        have htsub : t.val ⊆ s.val := h ▸ subset_union_right
        exact hne (eq_of_subset_of_card_le htsub (by rw [s.2, t.2])).symm
      rw [s.2] at hlt; omega
  have := card_union_add_card_inter s.val t.val
  rw [hU, s.2, t.2] at this
  omega
end Erdos835Palomar
