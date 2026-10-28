-- Prove2me | solution 1 for Erdos624.three_way_injection_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:53.067541+00:00
-- url     : https://prove2.me/submissions/d1aa8d51-1c5e-4dc4-90d3-33cc9dae974c

import Mathlib
open Finset

namespace E624R14T
open Finset

lemma small_count {ι β : Type*} [DecidableEq β] (X : Finset ι) (H : Finset β)
    (f : ι → Finset β) (hinj : Set.InjOn f X) (hsub : ∀ a ∈ X, f a ⊆ H) (m : ℕ) :
    #(X.filter (fun a => #(f a) ≤ m)) ≤ ∑ i ∈ range (m + 1), (#H).choose i := by
  have h1 : #(X.filter (fun a => #(f a) ≤ m)) ≤ #(H.powerset.filter (fun B => #B ≤ m)) := by
    apply card_le_card_of_injOn f
    · intro a ha
      rw [mem_coe, mem_filter] at ha ⊢
      exact ⟨mem_powerset.2 (hsub a ha.1), ha.2⟩
    · intro a ha b hb hab
      exact hinj (mem_filter.1 ha).1 (mem_filter.1 hb).1 hab
  have h2 : H.powerset.filter (fun B => #B ≤ m) = (range (m + 1)).biUnion (fun i => H.powersetCard i) := by
    ext B; simp only [mem_filter, mem_powerset, mem_biUnion, mem_range, mem_powersetCard]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨#B, by omega, h1, rfl⟩
    · rintro ⟨i, hi, h1, rfl⟩; exact ⟨h1, by omega⟩
  rw [h2] at h1
  refine h1.trans (card_biUnion_le.trans (le_of_eq (sum_congr rfl fun i _ => card_powersetCard _ _)))

theorem three {ι β : Type*} [DecidableEq β] (X : Finset ι) (H : Finset β)
    (f₁ f₂ f₃ : ι → Finset β)
    (h₁ : Set.InjOn f₁ X) (h₂ : Set.InjOn f₂ X) (h₃ : Set.InjOn f₃ X)
    (hsub : ∀ a ∈ X, f₁ a ⊆ H ∧ f₂ a ⊆ H ∧ f₃ a ⊆ H)
    (hpart : ∀ a ∈ X, #(f₁ a) + #(f₂ a) + #(f₃ a) ≤ #H) :
    #X ≤ 3 * ∑ i ∈ range (#H / 3 + 1), (#H).choose i := by
  classical
  have hcover : X ⊆ X.filter (fun a => #(f₁ a) ≤ #H / 3) ∪
      X.filter (fun a => #(f₂ a) ≤ #H / 3) ∪ X.filter (fun a => #(f₃ a) ≤ #H / 3) := by
    intro a ha
    have := hpart a ha
    simp only [mem_union, mem_filter]
    by_contra hc
    push Not at hc
    have := hc.1.1 ha; have := hc.1.2 ha; have := hc.2 ha
    omega
  have c1 := small_count X H f₁ h₁ (fun a ha => (hsub a ha).1) (#H / 3)
  have c2 := small_count X H f₂ h₂ (fun a ha => (hsub a ha).2.1) (#H / 3)
  have c3 := small_count X H f₃ h₃ (fun a ha => (hsub a ha).2.2) (#H / 3)
  have u1 := card_le_card hcover
  have u2 := card_union_le (X.filter (fun a => #(f₁ a) ≤ #H / 3) ∪
      X.filter (fun a => #(f₂ a) ≤ #H / 3)) (X.filter (fun a => #(f₃ a) ≤ #H / 3))
  have u3 := card_union_le (X.filter (fun a => #(f₁ a) ≤ #H / 3))
      (X.filter (fun a => #(f₂ a) ≤ #H / 3))
  omega

lemma third_sum (r : ℕ) :
    (∑ i ∈ range (r / 3 + 1), r.choose i) * 2 ^ r ≤ 2 ^ (r / 3) * 3 ^ r := by
  have h3 : (3 : ℕ) ^ r = ∑ i ∈ range (r + 1), r.choose i * 2 ^ (r - i) := by
    have := add_pow (1 : ℕ) 2 r
    rw [show (1 : ℕ) + 2 = 3 by norm_num] at this
    rw [this]; exact sum_congr rfl fun i _ => by rw [one_pow, one_mul, mul_comm, Nat.cast_id]
  rw [h3, mul_sum, sum_mul]
  calc ∑ i ∈ range (r / 3 + 1), r.choose i * 2 ^ r
      ≤ ∑ i ∈ range (r / 3 + 1), 2 ^ (r / 3) * (r.choose i * 2 ^ (r - i)) := by
        refine sum_le_sum fun i hi => ?_
        rw [mem_range] at hi
        have : 2 ^ r ≤ 2 ^ (r / 3) * 2 ^ (r - i) := by
          rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        calc r.choose i * 2 ^ r ≤ r.choose i * (2 ^ (r / 3) * 2 ^ (r - i)) :=
              Nat.mul_le_mul_left _ this
          _ = _ := by ring
    _ ≤ ∑ i ∈ range (r + 1), 2 ^ (r / 3) * (r.choose i * 2 ^ (r - i)) :=
        sum_le_sum_of_subset (range_subset_range.2 (by omega))

theorem third_tail (r : ℕ) :
    (∑ i ∈ range (r / 3 + 1), r.choose i) * 2 ^ r ≤ 2 ^ (r / 3) * 3 ^ r ∧
    (∑ i ∈ range (r / 3 + 1), r.choose i) ^ 51 ≤ 2 ^ (47 * r) := by
  refine ⟨third_sum r, ?_⟩
  set S := ∑ i ∈ range (r / 3 + 1), r.choose i
  have h1 := Nat.pow_le_pow_left (third_sum r) 51
  have h2 : (2 ^ (r / 3) * 3 ^ r) ^ 51 ≤ 2 ^ (98 * r) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm r 51, pow_mul 3]
    have h17 : (3 : ℕ) ^ 51 ≤ 2 ^ 81 := by norm_num
    calc 2 ^ (r / 3 * 51) * (3 ^ 51) ^ r ≤ 2 ^ (17 * r) * (2 ^ 81) ^ r := by
          apply Nat.mul_le_mul
          · exact Nat.pow_le_pow_right (by norm_num) (by omega)
          · exact Nat.pow_le_pow_left h17 r
      _ = 2 ^ (98 * r) := by rw [← pow_mul, ← pow_add]; ring_nf
  have h3 : S ^ 51 * 2 ^ (51 * r) ≤ 2 ^ (47 * r) * 2 ^ (51 * r) := by
    calc S ^ 51 * 2 ^ (51 * r) = (S * 2 ^ r) ^ 51 := by rw [mul_pow, ← pow_mul, mul_comm r 51]
      _ ≤ 2 ^ (98 * r) := h1.trans h2
      _ = 2 ^ (47 * r) * 2 ^ (51 * r) := by rw [← pow_add]; ring_nf
  exact le_of_mul_le_mul_right h3 (by positivity)
end E624R14T

namespace Erdos624

theorem three_way_injection_bound {ι β : Type*} [DecidableEq β] (X : Finset ι) (H : Finset β)
    (f₁ f₂ f₃ : ι → Finset β)
    (h₁ : Set.InjOn f₁ X) (h₂ : Set.InjOn f₂ X) (h₃ : Set.InjOn f₃ X)
    (hsub : ∀ a ∈ X, f₁ a ⊆ H ∧ f₂ a ⊆ H ∧ f₃ a ⊆ H)
    (hpart : ∀ a ∈ X, #(f₁ a) + #(f₂ a) + #(f₃ a) ≤ #H) :
    #X ≤ 3 * ∑ i ∈ range (#H / 3 + 1), (#H).choose i := by
  exact E624R14T.three X H f₁ f₂ f₃ h₁ h₂ h₃ hsub hpart

end Erdos624

open Finset

theorem solution {ι β : Type*} [DecidableEq β] (X : Finset ι) (H : Finset β)
    (f₁ f₂ f₃ : ι → Finset β)
    (h₁ : Set.InjOn f₁ X) (h₂ : Set.InjOn f₂ X) (h₃ : Set.InjOn f₃ X)
    (hsub : ∀ a ∈ X, f₁ a ⊆ H ∧ f₂ a ⊆ H ∧ f₃ a ⊆ H)
    (hpart : ∀ a ∈ X, #(f₁ a) + #(f₂ a) + #(f₃ a) ≤ #H) :
    #X ≤ 3 * ∑ i ∈ range (#H / 3 + 1), (#H).choose i :=
  Erdos624.three_way_injection_bound X H f₁ f₂ f₃ h₁ h₂ h₃ hsub hpart
