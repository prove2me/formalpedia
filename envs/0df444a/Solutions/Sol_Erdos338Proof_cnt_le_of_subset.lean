-- Prove2me | solution 1 for Erdos338Proof.cnt_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:21.847389+00:00
-- url     : https://prove2.me/submissions/4b4da13b-c21c-4c0c-ac0d-7461505874e2

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof
namespace Erdos338Proof
theorem _root_.solution {S : Set ℕ} {b c : ℕ} (h : ∀ x ∈ S, x < b → x < c) : cnt S b ≤ c := by
  classical
  unfold cnt
  calc #((range b).filter (· ∈ S)) ≤ #(range c) := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_range] at hx
        exact mem_range.2 (h x hx.2 hx.1)
    _ = c := card_range c
end Erdos338Proof
