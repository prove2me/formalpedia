-- Prove2me | solution 1 for Erdos287.compatible_slopes_dyadic_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:24:56.985265+00:00
-- url     : https://prove2.me/submissions/783764a7-564d-4cf3-b60b-b46e4139a685

import Mathlib

open Finset

set_option autoImplicit false

private theorem distinct_dyadic_valuations (a b : ℕ) (ha : 0 < a)
    (hab : a < b) (hcompat : b - a ∣ a) : padicValNat 2 a ≠ padicValNat 2 b := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro heq
  let e := padicValNat 2 a
  have haDiv : 2 ^ e ∣ a := (padicValNat_dvd_iff_le ha.ne').mpr le_rfl
  have hbDiv : 2 ^ e ∣ b := (padicValNat_dvd_iff_le (ha.trans hab).ne').mpr heq.le
  obtain ⟨u, hu⟩ := haDiv
  obtain ⟨v, hv⟩ := hbDiv
  have hnotA : ¬ 2 ^ (e + 1) ∣ a := by
    rw [padicValNat_dvd_iff_le ha.ne']
    change ¬ e + 1 ≤ e
    omega
  have hnotB : ¬ 2 ^ (e + 1) ∣ b := by
    rw [padicValNat_dvd_iff_le (ha.trans hab).ne', ← heq]
    change ¬ e + 1 ≤ e
    omega
  have huOdd : ¬ 2 ∣ u := by
    intro hU
    apply hnotA
    rw [hu, pow_succ]
    exact Nat.mul_dvd_mul_left _ hU
  have hvOdd : ¬ 2 ∣ v := by
    intro hV
    apply hnotB
    rw [hv, pow_succ]
    exact Nat.mul_dvd_mul_left _ hV
  have huv : u < v := by
    rw [hu, hv] at hab
    exact lt_of_mul_lt_mul_left hab (Nat.zero_le _)
  have hsub : 2 ∣ v - u := by
    rw [Nat.dvd_iff_mod_eq_zero] at huOdd hvOdd ⊢
    omega
  have hlarge : 2 ^ (e + 1) ∣ b - a := by
    rw [hv, hu, ← Nat.mul_sub_left_distrib, pow_succ]
    exact Nat.mul_dvd_mul_left _ hsub
  exact hnotA (hlarge.trans hcompat)

/-- Compatibility forces two different dyadic valuations on each edge.
A fully compatible set of size `k` contains a slope divisible by `2^(k-1)`. -/
theorem solution :
    (∀ a b : ℕ, 0 < a → a < b → b - a ∣ a → padicValNat 2 a ≠ padicValNat 2 b) ∧
    ∀ S : Finset ℕ, S.Nonempty → (∀ a ∈ S, 0 < a) →
      (∀ a ∈ S, ∀ b ∈ S, a < b → b - a ∣ a) →
      ∃ a ∈ S, 2 ^ (S.card - 1) ∣ a := by
  refine ⟨distinct_dyadic_valuations, ?_⟩
  intro S hS hpos hcompat
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Set.InjOn (padicValNat 2) (↑S : Set ℕ) := by
    intro a ha b hb heq
    rcases lt_trichotomy a b with h | h | h
    · exact (distinct_dyadic_valuations a b (hpos a ha) h (hcompat a ha b hb h) heq).elim
    · exact h
    · exact (distinct_dyadic_valuations b a (hpos b hb) h (hcompat b hb a ha h) heq.symm).elim
  by_contra! hn
  have hsub : S.image (padicValNat 2) ⊆ range (S.card - 1) := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    apply mem_range.mpr
    exact lt_of_not_ge fun h => hn a ha ((padicValNat_dvd_iff_le (hpos a ha).ne').mpr h)
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj, card_range] at hcard
  have hpositive := card_pos.mpr hS
  omega

