-- Prove2me | solution 1 for Erdos287.fixed_layer_blocked_cofactors_le_prime_progressions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:21:35.623801+00:00
-- url     : https://prove2.me/submissions/4d9ee162-4e0f-4c99-acd9-6a167f006ce3

import Mathlib

open Finset

set_option autoImplicit false

/-- For a fixed layer, the cofactors blocked by neighboring prime multiples
are bounded by prime counts in individual residue classes. -/
theorem solution (A C Q : Finset ℕ) (p L B : ℕ) (hp : 0 < p)
    (hA : ∀ a ∈ A, L ≤ a ∧ a ≤ B) (hC : ∀ b ∈ C, 0 < b) :
    let choices := C ×ˢ ({-1, 1} : Finset ℤ)
    let blocked := A.filter (fun a : ℕ => ∃ i ∈ choices, ∃ q ∈ Q,
      (a : ℤ) * p = (i.1 : ℤ) * q + i.2)
    let progression := fun i : ℕ × ℤ => Q.filter (fun q =>
      L * p ≤ i.1 * q + 1 ∧ q ≤ (B * p + 1) / i.1 ∧ (p : ℤ) ∣ (i.1 : ℤ) * q + i.2)
    blocked.card ≤ ∑ i ∈ choices, (progression i).card := by
  classical
  dsimp only
  let choices := C ×ˢ ({-1, 1} : Finset ℤ)
  let blockedBy (i : ℕ × ℤ) := A.filter (fun a : ℕ => ∃ q ∈ Q,
    (a : ℤ) * p = (i.1 : ℤ) * q + i.2)
  let progression (i : ℕ × ℤ) := Q.filter (fun q =>
    L * p ≤ i.1 * q + 1 ∧ q ≤ (B * p + 1) / i.1 ∧ (p : ℤ) ∣ (i.1 : ℤ) * q + i.2)
  change (A.filter (fun a : ℕ => ∃ i ∈ choices, ∃ q ∈ Q,
    (a : ℤ) * p = (i.1 : ℤ) * q + i.2)).card ≤ ∑ i ∈ choices, (progression i).card
  have hblocked : A.filter (fun a : ℕ => ∃ i ∈ choices, ∃ q ∈ Q,
      (a : ℤ) * p = (i.1 : ℤ) * q + i.2) = choices.biUnion blockedBy := by
    ext a
    simp only [mem_filter, mem_biUnion, blockedBy]
    constructor
    · rintro ⟨ha, i, hi, q, hq, hrel⟩
      exact ⟨i, hi, ha, q, hq, hrel⟩
    · rintro ⟨i, hi, ha, q, hq, hrel⟩
      exact ⟨ha, i, hi, q, hq, hrel⟩
  rw [hblocked]
  refine card_biUnion_le.trans (sum_le_sum fun i hi => ?_)
  obtain ⟨hib, hie⟩ := mem_product.mp hi
  have hb : 0 < i.1 := hC _ hib
  have he : -1 ≤ i.2 ∧ i.2 ≤ 1 := by
    simp only [mem_insert, mem_singleton] at hie
    rcases hie with h | h <;> omega
  have hwitness : ∀ a ∈ blockedBy i, ∃ q ∈ progression i,
      (a : ℤ) * p = (i.1 : ℤ) * q + i.2 := by
    intro a ha
    obtain ⟨haA, q, hqQ, hq⟩ := mem_filter.mp ha
    have hap₁ : (L : ℤ) * p ≤ (a : ℤ) * p := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hA a haA).1) (by positivity)
    have hap₂ : (a : ℤ) * p ≤ (B : ℤ) * p := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hA a haA).2) (by positivity)
    have hlower : L * p ≤ i.1 * q + 1 := by
      exact_mod_cast (show (L : ℤ) * p ≤ (i.1 : ℤ) * q + 1 by linarith [he.2])
    have hbq : (i.1 : ℤ) * q ≤ (B : ℤ) * p + 1 := by linarith [he.1]
    have hbound : q ≤ (B * p + 1) / i.1 := (Nat.le_div_iff_mul_le hb).mpr (by
      rw [mul_comm q i.1]
      exact_mod_cast hbq)
    refine ⟨q, mem_filter.mpr ⟨hqQ, hlower, hbound, ?_⟩, hq⟩
    rw [← hq]
    exact dvd_mul_left _ _
  choose q hq hrelation using hwitness
  let encode (a : ↥(blockedBy i)) := q a.val a.property
  have hmap : Set.MapsTo encode (↑(blockedBy i).attach : Set ↥(blockedBy i))
      (↑(progression i) : Set ℕ) := fun a _ => hq a.val a.property
  have hinj : Set.InjOn encode (↑(blockedBy i).attach : Set ↥(blockedBy i)) := by
    intro a _ a' _ h
    obtain ⟨a, ha⟩ := a
    obtain ⟨a', ha'⟩ := a'
    have hqeq : q a ha = q a' ha' := h
    have hm := hrelation a ha
    rw [hqeq, ← hrelation a' ha'] at hm
    have hz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
    have hvalue : a = a' := by exact_mod_cast mul_right_cancel₀ hz hm
    exact Subtype.ext hvalue
  simpa using card_le_card_of_injOn encode hmap hinj

