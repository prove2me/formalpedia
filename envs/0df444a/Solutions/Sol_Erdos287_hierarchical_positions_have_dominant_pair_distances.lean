-- Prove2me | solution 1 for Erdos287.hierarchical_positions_have_dominant_pair_distances
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:00:24.656925+00:00
-- url     : https://prove2.me/submissions/52598c4a-2120-4bbe-985b-ac0bc1dbb3e4

import Mathlib

open Finset

set_option autoImplicit false

/-- Binary subset sums of separated scales have each positive difference
close to one of those scales. -/
theorem solution (w : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j < k, 0 < w j)
    (hsep : ∀ j, j + 1 < k → 64 * w j ≤ w (j + 1)) :
    ∃ S : Finset ℕ, S.card = 2 ^ k ∧
      (∀ x ∈ S, x ≤ ∑ j ∈ Finset.range k, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < k,
        62 * w j ≤ 63 * (y - x) ∧ 63 * (y - x) ≤ 64 * w j := by
  have hsum (t : ℕ) (ht : t < k) : 63 * (∑ j ∈ range t, w j) ≤ w t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [sum_range_succ, mul_add]
      have h₁ := ih (by omega)
      have h₂ := hsep t ht
      omega
  have hex (t : ℕ) (ht : t ≤ k) : ∃ S : Finset ℕ, S.card = 2 ^ t ∧
      (∀ x ∈ S, x ≤ ∑ j ∈ range t, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < t,
        62 * w j ≤ 63 * (y - x) ∧ 63 * (y - x) ≤ 64 * w j := by
    induction t with
    | zero => exact ⟨{0}, by simp, by simp, by simp⟩
    | succ t ih =>
      obtain ⟨S, hS, hsmall, hdiff⟩ := ih (by omega)
      let R := S.image (fun x : ℕ => x + w t)
      have hwt := hpos t (by omega)
      have hdom := hsum t (by omega)
      have hdis : Disjoint S R := by
        apply disjoint_left.mpr
        intro x hx hxR
        obtain ⟨y, _, rfl⟩ := mem_image.mp hxR
        have hh := hsmall _ hx
        omega
      have hR : R.card = S.card :=
        card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
      refine ⟨S ∪ R, ?_, ?_, ?_⟩
      · rw [card_union_of_disjoint hdis, hR, hS, pow_succ, Nat.mul_two]
      · intro x hx
        rw [sum_range_succ]
        rcases mem_union.mp hx with hx | hx
        · exact (hsmall x hx).trans (Nat.le_add_right _ _)
        · obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
          exact Nat.add_le_add_right (hsmall y hy) _
      · intro x hx y hy hxy
        rcases mem_union.mp hx with hx | hxR <;> rcases mem_union.mp hy with hy | hyR
        · obtain ⟨j, hj, hlo, hhi⟩ := hdiff x hx y hy hxy
          exact ⟨j, by omega, hlo, hhi⟩
        · obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hyR
          have hx₀ := hsmall x hx
          have hy₁ := hsmall y₀ hy₀
          exact ⟨t, by omega, by omega, by omega⟩
        · obtain ⟨x₀, _, rfl⟩ := mem_image.mp hxR
          have hy₀ := hsmall y hy
          omega
        · obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hxR
          obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hyR
          obtain ⟨j, hj, hlo, hhi⟩ := hdiff x₀ hx₀ y₀ hy₀ (by omega)
          exact ⟨j, by omega, by omega, by omega⟩
  exact hex k le_rfl

