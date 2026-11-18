-- Prove2me | solution 1 for ContractionLemma.lemma_A_8_shifts_flip_one_bit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:22:56.095542+00:00
-- url     : https://prove2.me/submissions/d5b9a707-ad08-4c21-affd-ae02a906a984

import Mathlib

set_option autoImplicit false
namespace ContractionLemma

theorem lemma_A_8_shifts_flip_one_bit (a : ℕ) (t : ℤ) (ht : t ≠ 0) (x y : ℕ)
    (hx : x < 2 ^ a) (hy : y < 2 ^ a) (hxy : (y : ℤ) = x + t) :
    (∀ k < padicValInt 2 t, x.testBit k = y.testBit k) ∧
      x.testBit (padicValInt 2 t) ≠ y.testBit (padicValInt 2 t) := by
  have hdvd := padicValInt_dvd (p := 2) t
  have hiff := padicValInt_dvd_iff (p := 2) (padicValInt 2 t + 1) t
  generalize padicValInt 2 t = v at hdvd hiff ⊢
  obtain ⟨u, hu⟩ := hdvd
  push_cast at hu hiff
  have hnd : ¬ (2 : ℤ) ^ (v + 1) ∣ t := by
    rw [hiff]; omega
  have hodd : u % 2 = 1 := by
    by_contra h
    apply hnd
    obtain ⟨w, hw⟩ : (2 : ℤ) ∣ u := by omega
    exact ⟨w, by rw [hu, hw]; ring⟩
  have key : ∀ k, k ≤ v → (y : ℤ) / 2 ^ k = (x : ℤ) / 2 ^ k + 2 ^ (v - k) * u := by
    intro k hk
    rw [hxy, hu]
    have : (2 : ℤ) ^ v * u = 2 ^ (v - k) * u * 2 ^ k := by
      have h2 : (2 : ℤ) ^ v = 2 ^ (v - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
      rw [h2]; ring
    rw [this, Int.add_mul_ediv_right _ _ (by positivity)]
  have hbit : ∀ (n k : ℕ), n.testBit k = decide (((n : ℤ) / 2 ^ k) % 2 = 1) := by
    intro n k
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have : ((n : ℤ) / 2 ^ k) = ((n / 2 ^ k : ℕ) : ℤ) := by push_cast; rfl
    rw [this]
    simp only [decide_eq_decide]
    omega
  constructor
  · intro k hk
    have hk' : k < v := hk
    rw [hbit x k, hbit y k, key k hk'.le]
    have hev : (2 : ℤ) ^ (v - k) * u % 2 = 0 := by
      have : (2 : ℤ) ^ (v - k) = 2 * 2 ^ (v - k - 1) := by
        have hvk : v - k = (v - k - 1) + 1 := by omega
        rw [hvk, pow_succ', Nat.add_sub_cancel]
      rw [this, mul_assoc]; omega
    simp only [decide_eq_decide]
    omega
  · rw [hbit x v, hbit y v, key v le_rfl, Nat.sub_self, pow_zero, one_mul]
    simp only [ne_eq, decide_eq_decide]
    omega

end ContractionLemma

theorem solution (a : ℕ) (t : ℤ) (ht : t ≠ 0) (x y : ℕ)
    (hx : x < 2 ^ a) (hy : y < 2 ^ a) (hxy : (y : ℤ) = x + t) :
    (∀ k < padicValInt 2 t, x.testBit k = y.testBit k) ∧
      x.testBit (padicValInt 2 t) ≠ y.testBit (padicValInt 2 t) :=
  ContractionLemma.lemma_A_8_shifts_flip_one_bit a t ht x y hx hy hxy
