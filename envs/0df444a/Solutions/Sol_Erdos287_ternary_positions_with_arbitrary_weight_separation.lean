-- Prove2me | solution 1 for Erdos287.ternary_positions_with_arbitrary_weight_separation
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:11:38.463525+00:00
-- url     : https://prove2.me/submissions/a1c47d4f-03cd-4a99-8482-d196a7510390

import Mathlib

open Finset

set_option autoImplicit false

/-- Ternary positions inherit pair-distance bounds from arbitrarily
separated positive weights. The parameter r is one less than the separation factor. -/
theorem solution (w : ℕ → ℕ) (k r : ℕ) (hr : 2 < r)
    (hpos : ∀ j < k, 0 < w j)
    (hsep : ∀ j, j + 1 < k → (r + 1) * w j ≤ w (j + 1)) :
    ∃ S : Finset ℕ, S.card = 3 ^ k ∧
      (∀ x ∈ S, x ≤ 2 * ∑ j ∈ Finset.range k, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < k,
        r * w j ≤ r * (y - x) + 2 * w j ∧
        r * (y - x) ≤ r * (2 * w j) + 2 * w j := by
  have hsum (t : ℕ) (ht : t < k) : r * (∑ j ∈ range t, w j) ≤ w t := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [sum_range_succ, mul_add]
      have h₁ := ih (by omega)
      have h₂ := hsep t ht
      rw [add_mul, one_mul] at h₂
      omega
  have hex (t : ℕ) (ht : t ≤ k) : ∃ S : Finset ℕ, S.card = 3 ^ t ∧
      (∀ x ∈ S, x ≤ 2 * ∑ j ∈ range t, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < t,
        r * w j ≤ r * (y - x) + 2 * w j ∧
          r * (y - x) ≤ r * (2 * w j) + 2 * w j := by
    induction t with
    | zero => exact ⟨{0}, by simp, by simp, by simp⟩
    | succ t ih =>
      obtain ⟨S, hS, hsmall, hdiff⟩ := ih (by omega)
      let D := range 3
      let R (d : ℕ) := S.image (fun x : ℕ => x + d * w t)
      have hwt := hpos t (by omega)
      have hdom := hsum t (by omega)
      have hdom' : 2 * (∑ j ∈ range t, w j) < w t := by
        by_cases hzero : (∑ j ∈ range t, w j) = 0
        · simpa [hzero] using hwt
        · exact (Nat.mul_lt_mul_of_pos_right hr (Nat.pos_of_ne_zero hzero)).trans_le hdom
      have hord (d e x y : ℕ) (hde : d < e) (hx : x ∈ R d) (hy : y ∈ R e) : x < y := by
        obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
        obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hy
        have hx := hsmall x₀ hx₀
        have hshift := Nat.mul_le_mul_right (w t) (show d + 1 ≤ e by omega)
        rw [add_mul, one_mul] at hshift
        omega
      have hpair : (↑D : Set ℕ).PairwiseDisjoint R := by
        intro d hd e he hne
        apply disjoint_left.mpr
        intro x hx hy
        rcases lt_or_gt_of_ne hne with h | h
        · exact (lt_irrefl x) (hord d e x x h hx hy)
        · exact (lt_irrefl x) (hord e d x x h hy hx)
      have hR (d : ℕ) : (R d).card = S.card :=
        card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)
      refine ⟨D.biUnion R, ?_, ?_, ?_⟩
      · rw [card_biUnion hpair]
        simp [D, hR, hS, pow_succ, mul_comm]
      · intro x hx
        obtain ⟨d, hd, hx⟩ := mem_biUnion.mp hx
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
        have hdm := Nat.mul_le_mul_right (w t) (show d ≤ 2 by
          have hd' : d < 3 := mem_range.mp hd
          omega)
        have hys := hsmall y hy
        rw [sum_range_succ, mul_add]
        omega
      · intro x hx y hy hxy
        obtain ⟨d, hd, hx⟩ := mem_biUnion.mp hx
        obtain ⟨e, he, hy⟩ := mem_biUnion.mp hy
        by_cases hde : d = e
        · subst e
          obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
          obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hy
          obtain ⟨j, hj, hlo, hhi⟩ := hdiff x₀ hx₀ y₀ hy₀ (by omega)
          have hshift : y₀ + d * w t - (x₀ + d * w t) = y₀ - x₀ := by omega
          rw [hshift]
          exact ⟨j, by omega, hlo, hhi⟩
        · have hlt : d < e := by
            rcases lt_or_gt_of_ne hde with h | h
            · exact h
            · exact False.elim ((hord e d y x h hy hx).asymm hxy)
          obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hx
          obtain ⟨y₀, hy₀, rfl⟩ := mem_image.mp hy
          have hx₀' := hsmall x₀ hx₀
          have hy₀' := hsmall y₀ hy₀
          have he' : e < 3 := mem_range.mp he
          have hlow := Nat.mul_le_mul_right (w t) (show 1 ≤ e - d by omega)
          have hupp := Nat.mul_le_mul_right (w t) (show e - d ≤ 2 by omega)
          have hid : (e - d) * w t + d * w t = e * w t := by
            rw [← add_mul, Nat.sub_add_cancel hlt.le]
          rw [one_mul] at hlow
          have htail : r * (2 * (∑ j ∈ range t, w j)) ≤ 2 * w t := by
            rw [← mul_assoc, mul_comm r 2, mul_assoc]
            exact Nat.mul_le_mul_left 2 hdom
          have hleft := (Nat.mul_le_mul_left r hx₀').trans htail
          have hright := (Nat.mul_le_mul_left r hy₀').trans htail
          have h₁ := Nat.mul_le_mul_left r (show w t ≤
            (y₀ + e * w t - (x₀ + d * w t)) + x₀ by omega)
          have h₂ := Nat.mul_le_mul_left r (show
            y₀ + e * w t - (x₀ + d * w t) ≤ 2 * w t + y₀ by omega)
          rw [mul_add] at h₁ h₂
          exact ⟨t, by omega, by omega, by omega⟩
  exact hex k le_rfl

