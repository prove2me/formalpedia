-- Prove2me | solution 1 for Erdos624.odd_subsets_span_parity_space
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:10:42.369855+00:00
-- url     : https://prove2.me/submissions/34e7eb24-47d1-44a4-881b-8abb8debef56

import Mathlib
open Finset

namespace E624R15S
open Finset

lemma chi_insert {U : Type*} [DecidableEq U] (Y : Finset U) (x : U) (hx : x ∉ Y) :
    (fun y => if y ∈ insert x Y then (1 : ZMod 2) else 0) =
      Pi.single x 1 + (fun y => if y ∈ Y then (1 : ZMod 2) else 0) := by
  ext y
  by_cases h : y = x
  · subst h; simp [hx]
  · simp [h, Pi.single_apply]

lemma chi_eq_sum {U : Type*} [DecidableEq U] (Y : Finset U) :
    (fun y => if y ∈ Y then (1 : ZMod 2) else 0) = ∑ x ∈ Y, Pi.single x 1 := by
  ext y; simp [Finset.sum_apply, Pi.single_apply]

theorem odd_span {U : Type*} [DecidableEq U] (k : ℕ) (hk : Odd k) (Q : Finset U)
    (hQ : k + 1 ≤ #Q) (f : U → ZMod 2) (hf : ∀ y, f y ≠ 0 → y ∈ Q) :
    f ∈ Submodule.span (ZMod 2)
      {g | ∃ Y ⊆ Q, #Y = k ∧ g = fun y => if y ∈ Y then (1 : ZMod 2) else 0} := by
  set S := Submodule.span (ZMod 2)
      {g | ∃ Y ⊆ Q, #Y = k ∧ g = fun y => if y ∈ Y then (1 : ZMod 2) else 0} with hS
  have hmem : ∀ Y ⊆ Q, #Y = k → (fun y => if y ∈ Y then (1 : ZMod 2) else 0) ∈ S :=
    fun Y hY hc => Submodule.subset_span ⟨Y, hY, hc, rfl⟩
  -- differences of unit vectors
  have hpair : ∀ x ∈ Q, ∀ y ∈ Q, (Pi.single x 1 + Pi.single y 1 : U → ZMod 2) ∈ S := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      have : (Pi.single x 1 + Pi.single x 1 : U → ZMod 2) = 0 := by
        rw [← Pi.single_add]; rw [show (1 : ZMod 2) + 1 = 0 by decide, Pi.single_zero]
      rw [this]; exact S.zero_mem
    obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq (s := (Q.erase x).erase y) (n := k - 1) (by
      rw [card_erase_of_mem (mem_erase.2 ⟨Ne.symm hxy, hy⟩), card_erase_of_mem hx]; omega)
    have hxY : x ∉ Y := fun h => by have := hY h; simp at this
    have hyY : y ∉ Y := fun h => by have := hY h; simp at this
    have hYQ : Y ⊆ Q := hY.trans ((erase_subset _ _).trans (erase_subset _ _))
    have hk1 : 1 ≤ k := hk.pos
    have h1 := hmem (insert x Y) (insert_subset hx hYQ) (by rw [card_insert_of_notMem hxY]; omega)
    have h2 := hmem (insert y Y) (insert_subset hy hYQ) (by rw [card_insert_of_notMem hyY]; omega)
    have := S.add_mem h1 h2
    rw [chi_insert Y x hxY, chi_insert Y y hyY] at this
    convert this using 1
    have e : ∀ v : U → ZMod 2, v + v = 0 := fun v => by ext; simp [ZModModule.add_self]
    have := e (fun y => if y ∈ Y then (1 : ZMod 2) else 0)
    rw [add_add_add_comm, this, add_zero]
  obtain ⟨Y0, hY0, hY0c⟩ := exists_subset_card_eq (s := Q) (n := k) (by omega)
  have hunit : ∀ x ∈ Q, (Pi.single x 1 : U → ZMod 2) ∈ S := by
    intro x hx
    have hsum : (Pi.single x 1 : U → ZMod 2) =
        (fun y => if y ∈ Y0 then (1 : ZMod 2) else 0) +
          ∑ y ∈ Y0, (Pi.single x 1 + Pi.single y 1 : U → ZMod 2) := by
      rw [sum_add_distrib, sum_const, hY0c, chi_eq_sum]
      obtain ⟨t, rfl⟩ := hk
      rw [show 2 * t + 1 = 1 + 2 * t by ring, add_nsmul, one_nsmul, mul_nsmul]
      have e2 : (2 : ℕ) • (Pi.single x 1 : U → ZMod 2) = 0 := by
        rw [two_nsmul]; ext; simp [ZModModule.add_self]
      rw [e2, smul_zero, add_zero]
      have e : ∀ v : U → ZMod 2, v + v = 0 := fun v => by ext; simp [ZModModule.add_self]
      rw [add_left_comm, e, add_zero]
    rw [hsum]
    exact S.add_mem (hmem Y0 hY0 hY0c) (S.sum_mem fun y hy => hpair x hx y (hY0 hy))
  have hf' : f = ∑ x ∈ Q, f x • (Pi.single x 1 : U → ZMod 2) := by
    ext y
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, sum_ite_eq, sum_ite_eq']
    split_ifs with h
    · rfl
    · by_contra hc; exact h (hf y (Ne.symm hc |>.symm))
  rw [hf']
  exact S.sum_mem fun x hx => S.smul_mem _ (hunit x hx)
end E624R15S

namespace Erdos624

theorem odd_subsets_span_parity_space {U : Type*} [DecidableEq U] (k : ℕ) (hk : Odd k) (Q : Finset U)
    (hQ : k + 1 ≤ #Q) (f : U → ZMod 2) (hf : ∀ y, f y ≠ 0 → y ∈ Q) :
    f ∈ Submodule.span (ZMod 2)
      {g | ∃ Y ⊆ Q, #Y = k ∧ g = fun y => if y ∈ Y then (1 : ZMod 2) else 0} := by
  exact E624R15S.odd_span k hk Q hQ f hf

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] (k : ℕ) (hk : Odd k) (Q : Finset U)
    (hQ : k + 1 ≤ #Q) (f : U → ZMod 2) (hf : ∀ y, f y ≠ 0 → y ∈ Q) :
    f ∈ Submodule.span (ZMod 2)
      {g | ∃ Y ⊆ Q, #Y = k ∧ g = fun y => if y ∈ Y then (1 : ZMod 2) else 0} :=
  Erdos624.odd_subsets_span_parity_space k hk Q hQ f hf
