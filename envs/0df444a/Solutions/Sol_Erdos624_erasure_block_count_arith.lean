-- Prove2me | solution 1 for Erdos624.erasure_block_count_arith
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:29:24.303291+00:00
-- url     : https://prove2.me/submissions/7b8ec1f2-f58e-4ca7-8e35-baa064fd9602

import Mathlib
open Finset

namespace E624R12
open Finset

lemma four_mul_le_two_pow (k : ℕ) (hk : 4 ≤ k) : 4 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem erasure_arith (k : ℕ) (hk : 4 ≤ k) :
    4 * k ≤ 2 ^ k ∧ 2 ^ k < 2 * k * ((2 ^ k - k + 1) / (k - 3)) ∧
      2 ^ k < 256 * k * ((2 ^ k - k + 1) / (k - 3)) := by
  have h4 := four_mul_le_two_pow k hk
  refine ⟨h4, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
  have hd : j + 4 - 3 = j + 1 := by omega
  rw [hd]
  set n := 2 ^ (j + 4) with hn
  set N' := n - (j + 4) + 1 with hN'
  have hN'e : N' + j + 3 = n := by omega
  have hdm := Nat.div_add_mod N' (j + 1)
  have hr := Nat.mod_lt N' (show 0 < j + 1 by omega)
  set t := N' / (j + 1)
  set r := N' % (j + 1)
  have h2 : n < 2 * (j + 4) * t := by
    by_contra hcon
    push Not at hcon
    have hm : 2 * (j + 4) * t * (j + 1) ≤ n * (j + 1) := Nat.mul_le_mul_right _ hcon
    nlinarith
  refine ⟨h2, ?_⟩
  nlinarith

theorem erasure_lower_bound {U : Type*} [DecidableEq U] (t : ℕ) (P : Fin t → Finset U)
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (E1 E2 E3 : Fin t → Finset U) (h1 : ∀ j, E1 j ⊆ P j) (h2 : ∀ j, E2 j ⊆ P j)
    (h3 : ∀ j, E3 j ⊆ P j)
    (hZ : ∀ j x, ((if x ∈ E1 j then 1 else 0) + (if x ∈ E2 j then 1 else 0) +
      (if x ∈ E3 j then 1 else 0) : ZMod 2) = 0)
    (R : Finset U) (w : U → ZMod 2)
    (hw : ∀ j, (Disjoint (E1 j) R → ∑ x ∈ E1 j, w x = 1) ∧
      (Disjoint (E2 j) R → ∑ x ∈ E2 j, w x = 1) ∧ (Disjoint (E3 j) R → ∑ x ∈ E3 j, w x = 1)) :
    t ≤ #R := by
  have hsum : ∀ j, ∀ E ⊆ P j, ∑ x ∈ E, w x = ∑ x ∈ P j, w x * (if x ∈ E then 1 else 0) := by
    intro j E hE
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter]; congr 1; ext x; simp only [mem_filter]
    exact ⟨fun h => ⟨hE h, h⟩, fun h => h.2⟩
  have hmeet : ∀ j, ∃ x ∈ R, x ∈ P j := by
    intro j
    by_contra hcon
    push Not at hcon
    have hd : ∀ E ⊆ P j, Disjoint E R := by
      intro E hE
      rw [disjoint_left]; intro x hx hxR; exact hcon x hxR (hE hx)
    have e1 := (hw j).1 (hd _ (h1 j))
    have e2 := (hw j).2.1 (hd _ (h2 j))
    have e3 := (hw j).2.2 (hd _ (h3 j))
    rw [hsum j _ (h1 j)] at e1
    rw [hsum j _ (h2 j)] at e2
    rw [hsum j _ (h3 j)] at e3
    have : ∑ x ∈ P j, w x * (if x ∈ E1 j then 1 else 0) + ∑ x ∈ P j, w x * (if x ∈ E2 j then 1 else 0)
        + ∑ x ∈ P j, w x * (if x ∈ E3 j then 1 else 0) = 0 := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_eq_zero; intro x _
      rw [← mul_add, ← mul_add, hZ j x, mul_zero]
    rw [e1, e2, e3] at this
    exact absurd this (by decide)
  choose f hfR hfP using hmeet
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact disjoint_left.1 (hP i j hne) (hfP i) (hij ▸ hfP j)
  calc t = #(univ.image f) := by rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    _ ≤ #R := card_le_card (by intro x hx; obtain ⟨j, _, rfl⟩ := mem_image.1 hx; exact hfR j)
end E624R12

namespace Erdos624

theorem erasure_block_count_arith (k : ℕ) (hk : 4 ≤ k) :
    4 * k ≤ 2 ^ k ∧ 2 ^ k < 2 * k * ((2 ^ k - k + 1) / (k - 3)) ∧
      2 ^ k < 256 * k * ((2 ^ k - k + 1) / (k - 3)) := by
  exact E624R12.erasure_arith k hk

end Erdos624

open Finset

theorem solution (k : ℕ) (hk : 4 ≤ k) :
    4 * k ≤ 2 ^ k ∧ 2 ^ k < 2 * k * ((2 ^ k - k + 1) / (k - 3)) ∧
      2 ^ k < 256 * k * ((2 ^ k - k + 1) / (k - 3)) :=
  Erdos624.erasure_block_count_arith k hk
