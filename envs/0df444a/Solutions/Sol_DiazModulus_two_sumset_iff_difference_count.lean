-- Prove2me | solution 1 for DiazModulus.two_sumset_iff_difference_count
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:42:37.77643+00:00
-- url     : https://prove2.me/submissions/26890132-f5a0-47bf-9daf-2ea3be4b834f

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Two-element sumsets inside a finite set of integers

A sumset `A + B ⊆ S` with `#A = 2` and `#B = q` exists iff some positive difference `d` is realised
by at least `q` elements of `S`, i.e. `q ≤ #{s ∈ S | s + d ∈ S}`.

Forward: write `A = {a, b}` with `a < b` and put `d = b - a`. Then `a + x ∈ S` and `b + x ∈ S` for
every `x ∈ B`, so the translate `B + a` (of cardinality `q`) lies in `{s ∈ S | s + d ∈ S}`.
Backward: choose `B ⊆ {s ∈ S | s + d ∈ S}` with `#B = q` (`Finset.exists_subset_card_eq`) and take
`A = {0, d}`; then `0 + s` and `d + s` lie in `S` for every `s ∈ B`. The case `q = 0` is included.
-/

namespace R6_twoSumset

open Pointwise

/-- The forward direction for `A = {a, b}` with `a < b`. -/
theorem forward (S B : Finset ℤ) (a b : ℤ) (hab : a < b) (hAB : ({a, b} : Finset ℤ) + B ⊆ S) :
    ∃ d : ℤ, 0 < d ∧ B.card ≤ (S.filter (fun s => s + d ∈ S)).card := by
  refine ⟨b - a, by omega, ?_⟩
  have hsub : B.image (· + a) ⊆ S.filter (fun s => s + (b - a) ∈ S) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    rw [Finset.mem_filter]
    constructor
    · rw [add_comm]
      exact hAB (Finset.add_mem_add (by simp) hx)
    · have : x + a + (b - a) = b + x := by ring
      rw [this]
      exact hAB (Finset.add_mem_add (by simp) hx)
  calc B.card = (B.image (· + a)).card :=
        (Finset.card_image_of_injective _ (add_left_injective a)).symm
    _ ≤ _ := Finset.card_le_card hsub

end R6_twoSumset

open DiazModulus R6_twoSumset Pointwise in
theorem solution (S : Finset ℤ) (q : ℕ) :
    (∃ A B : Finset ℤ, A.card = 2 ∧ B.card = q ∧ A + B ⊆ S) ↔
      ∃ d : ℤ, 0 < d ∧ q ≤ (S.filter (fun s => s + d ∈ S)).card := by
  constructor
  · rintro ⟨A, B, hA, rfl, hAB⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hA
    rcases lt_or_gt_of_ne hab with h | h
    · exact forward S B a b h hAB
    · exact forward S B b a h (by rwa [Finset.pair_comm])
  · rintro ⟨d, hd, hq⟩
    obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hq
    refine ⟨{0, d}, B, Finset.card_pair (by omega), hBc, ?_⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hz
    have hyS := Finset.mem_filter.1 (hB hy)
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hyS.1
    · rw [Finset.mem_singleton.1 hx, add_comm]
      exact hyS.2
