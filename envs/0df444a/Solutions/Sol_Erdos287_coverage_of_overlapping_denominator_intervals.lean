-- Prove2me | solution 1 for Erdos287.coverage_of_overlapping_denominator_intervals
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:45:34.424151+00:00
-- url     : https://prove2.me/submissions/779161f4-b6d1-48b5-a267-64b5d93cd9d6

import Mathlib

open Finset

set_option autoImplicit false

/-- Adjacent positions in the hull of two overlapping denominator intervals
are covered by one of the original intervals. -/
theorem solution (D E : Finset ℕ) (a b c d : ℕ) (hacross : a ≤ d) (hccross : c ≤ b)
    (hD : ∀ x, a ≤ x → x + 1 ≤ b → x ∈ D ∨ x + 1 ∈ D)
    (hE : ∀ x, c ≤ x → x + 1 ≤ d → x ∈ E ∨ x + 1 ∈ E) :
    ∀ x, min a c ≤ x → x + 1 ≤ max b d → x ∈ D ∪ E ∨ x + 1 ∈ D ∪ E := by
  intro x hlo hhi
  by_cases hxa : a ≤ x
  · by_cases hxb : x + 1 ≤ b
    · rcases hD x hxa hxb with h | h
      · exact Or.inl (mem_union_left E h)
      · exact Or.inr (mem_union_left E h)
    · have hxc : c ≤ x := hccross.trans (by omega)
      have hxd : x + 1 ≤ d := by omega
      rcases hE x hxc hxd with h | h
      · exact Or.inl (mem_union_right D h)
      · exact Or.inr (mem_union_right D h)
  · have hxc : c ≤ x := by omega
    have hxd : x + 1 ≤ d := by omega
    rcases hE x hxc hxd with h | h
    · exact Or.inl (mem_union_right D h)
    · exact Or.inr (mem_union_right D h)

