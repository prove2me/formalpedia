-- Prove2me | solution 1 for Erdos287.card_bound_for_close_maximum_cluster
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:45:45.4817+00:00
-- url     : https://prove2.me/submissions/f60c4823-0bd5-458f-8d05-e9786b94fd02

import Mathlib

open Finset

set_option autoImplicit false

/-- A set of maxima in a multiplicative cluster has a sharp linear bound
for its cardinality in a prefix. -/
theorem solution (S : Finset ℕ) (N : ℕ) (hN : ∀ x ∈ S, x ≤ N)
    (hclose : ∀ x ∈ S, ∀ y ∈ S, 80 * y < 87 * x) :
    87 * S.card ≤ 7 * N + 87 := by
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha : a ∈ S := min'_mem S hS
    have hb : b ∈ S := max'_mem S hS
    have hab : a ≤ b := min'_le S b hb
    have hspan : S ⊆ Icc a b := fun n hn => mem_Icc.mpr ⟨min'_le S n hn, le_max' S n hn⟩
    have hcard := card_le_card hspan
    rw [Nat.card_Icc] at hcard
    have hratio := hclose a ha b hb
    have hbound := hN b hb
    omega
  · rw [not_nonempty_iff_eq_empty.mp hS, card_empty]
    simp

