-- Prove2me | solution 1 for Erdos624.strict_half_measure_multicover_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:49.829237+00:00
-- url     : https://prove2.me/submissions/a2fbb66f-287f-4b75-8ade-96104b12a419

import Mathlib
open Finset

namespace E624R14C
open Finset

lemma avg {α ι : Type*} [DecidableEq α] (w : α → ℝ) (X : Finset α) (I : Finset ι)
    (B : ι → Finset α) :
    ∑ x ∈ X, w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) =
      ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x := by
  simp_rw [card_filter, Nat.cast_sum, mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

lemma step {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (X : Finset α)
    (I : Finset ι) (B : ι → Finset α) (x : α) (hx : x ∈ X)
    (hcov : ∀ S ⊆ X, #S ≤ s + 1 → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    ∀ S ⊆ X.erase x, #S ≤ s →
      lam ≤ #((I.filter (fun i => x ∈ B i)).filter (fun i => S ⊆ B i)) := by
  intro S hS hs
  have hxS : x ∉ S := fun h => by have := hS h; simp at this
  have := hcov (insert x S) (insert_subset hx (hS.trans (erase_subset _ _)))
    (by rw [card_insert_of_notMem hxS]; omega)
  convert this using 2
  ext i; simp [insert_subset_iff]; tauto

lemma sub_measure {α ι : Type*} [DecidableEq α] (w : α → ℝ) (X : Finset α)
    (B : ι → Finset α) (x : α) (hx : x ∈ X) (i : ι) (hi : x ∈ B i) :
    ∑ y ∈ (X.erase x).filter (fun y => y ∈ B i), w y =
      ∑ y ∈ X.filter (fun y => y ∈ B i), w y - w x := by
  have hm : x ∈ X.filter (fun y => y ∈ B i) := mem_filter.2 ⟨hx, hi⟩
  rw [← sum_erase_add _ _ hm, filter_erase]; ring

theorem strict {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam : ℕ) (hlam : 1 ≤ lam) :
    ∀ (s : ℕ) (X : Finset α) (I : Finset ι) (B : ι → Finset α),
      (∀ x ∈ X, 0 < w x) →
      (∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x < ∑ x ∈ X, w x) →
      (∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) →
      (lam + 1) * 2 ^ s ≤ #I + 1 := by
  intro s
  induction s with
  | zero =>
    intro X I B _ _ hcov
    have := hcov ∅ (empty_subset _) (by simp)
    simp at this; simp; omega
  | succ s ih =>
    intro X I B hw hmeas hcov
    have hI : lam ≤ #I := by
      have := hcov ∅ (empty_subset _) (by simp); simpa using this
    have hXne : X.Nonempty := by
      by_contra hX
      rw [not_nonempty_iff_eq_empty] at hX
      obtain ⟨i, hi⟩ : I.Nonempty := card_pos.1 (by omega)
      have := hmeas i hi; simp [hX] at this
    have hW : 0 < ∑ x ∈ X, w x := sum_pos hw hXne
    have hd : ∀ x ∈ X, (lam + 1) * 2 ^ s ≤ #(I.filter (fun i => x ∈ B i)) + 1 := by
      intro x hx
      refine ih (X.erase x) _ B (fun y hy => hw y (mem_of_mem_erase hy)) ?_
        (step w lam s X I B x hx hcov)
      intro i hi
      rw [mem_filter] at hi
      rw [sub_measure w X B x hx i hi.2]
      have := hmeas i hi.1
      have e := sum_erase_add X w hx
      linarith [hw x hx]
    -- averaging
    set D : ℝ := ((lam + 1) * 2 ^ s : ℕ) - 1 with hD
    have h1 : D * ∑ x ∈ X, w x ≤ ∑ x ∈ X, w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun x hx => ?_
      have := hd x hx
      have : D ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
        rw [hD]; have h' : ((lam + 1) * 2 ^ s : ℕ) ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) + 1 := by
          exact_mod_cast this
        linarith
      nlinarith [hw x hx]
    rw [avg] at h1
    have hIne : I.Nonempty := card_pos.1 (by omega)
    have h2 : 2 * ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x < #I * ∑ x ∈ X, w x := by
      rw [mul_sum, ← nsmul_eq_mul, ← sum_const]
      exact sum_lt_sum_of_nonempty hIne fun i hi => hmeas i hi
    have h3 : 2 * D < #I := by
      by_contra hc; push Not at hc
      nlinarith
    have h4 : (((lam + 1) * 2 ^ (s + 1) : ℕ) : ℝ) < #I + 2 := by
      rw [hD] at h3; push_cast at h3 ⊢; rw [pow_succ]; linarith
    have h5 : (lam + 1) * 2 ^ (s + 1) < #I + 2 := by exact_mod_cast h4
    omega

theorem half {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (hlam : 1 ≤ lam)
    (hs : 1 ≤ s) (X : Finset α) (hX : X.Nonempty) (I : Finset ι) (B : ι → Finset α)
    (hw : ∀ x ∈ X, 0 < w x)
    (hmeas : ∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 2 := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hW : 0 < ∑ x ∈ X, w x := sum_pos hw hX
  have hd : ∀ x ∈ X, (lam + 1) * 2 ^ s ≤ #(I.filter (fun i => x ∈ B i)) + 1 := by
    intro x hx
    refine strict w lam hlam s (X.erase x) _ B (fun y hy => hw y (mem_of_mem_erase hy)) ?_
      (step w lam s X I B x hx hcov)
    intro i hi
    rw [mem_filter] at hi
    rw [sub_measure w X B x hx i hi.2]
    have := hmeas i hi.1
    have e := sum_erase_add X w hx
    linarith [hw x hx]
  set D : ℝ := ((lam + 1) * 2 ^ s : ℕ) - 1 with hD
  have h1 : D * ∑ x ∈ X, w x ≤ ∑ x ∈ X, w x * (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    have := hd x hx
    have : D ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) := by
      rw [hD]; have h' : ((lam + 1) * 2 ^ s : ℕ) ≤ (#(I.filter (fun i => x ∈ B i)) : ℝ) + 1 := by
        exact_mod_cast this
      linarith
    nlinarith [hw x hx]
  rw [avg] at h1
  have h2 : 2 * ∑ i ∈ I, ∑ x ∈ X.filter (fun x => x ∈ B i), w x ≤ #I * ∑ x ∈ X, w x := by
    rw [mul_sum, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi => hmeas i hi
  have h3 : 2 * D ≤ #I := by
    by_contra hc; push Not at hc
    nlinarith
  have h4 : (((lam + 1) * 2 ^ (s + 1) : ℕ) : ℝ) ≤ #I + 2 := by
    rw [hD] at h3; push_cast at h3 ⊢; rw [pow_succ]; linarith
  exact_mod_cast h4
end E624R14C

namespace Erdos624

theorem strict_half_measure_multicover_bound {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (hlam : 1 ≤ lam)
    (X : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hw : ∀ x ∈ X, 0 < w x)
    (hmeas : ∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x < ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 1 := by
  exact E624R14C.strict w lam hlam s X I B hw hmeas hcov

end Erdos624

open Finset

theorem solution {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (hlam : 1 ≤ lam)
    (X : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hw : ∀ x ∈ X, 0 < w x)
    (hmeas : ∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x < ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 1 :=
  Erdos624.strict_half_measure_multicover_bound w lam s hlam X I B hw hmeas hcov
