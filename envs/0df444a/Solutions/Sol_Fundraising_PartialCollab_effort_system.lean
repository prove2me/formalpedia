-- Prove2me | solution 1 for Fundraising.PartialCollab.effort_system
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T16:06:29.502552+00:00
-- url     : https://prove2.me/submissions/41f5f2d5-5e27-4b8a-93d7-70d06c1de7b1

import Mathlib
import Definitions.Def_Fundraising_PartialCollab_Setting

namespace Fundraising.PartialCollab

open Finset

theorem kbar_iff {n : ℕ} [NeZero n] (α : Fin n → ℝ) (hα : Antitone α) (i : Fin n) :
    (i : ℕ) < kbar α ↔ α i = α 0 := by
  unfold kbar
  constructor
  · intro hi
    by_contra hne
    have hsub : (univ.filter fun j : Fin n => α j = α 0) ⊆ Finset.Iio i := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hji
      push Not at hji
      apply hne
      have h1 : α j ≤ α i := hα hji
      have h2 : α i ≤ α 0 := hα (Fin.zero_le i)
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hi
    have hsub : Finset.Iic i ⊆ (univ.filter fun j : Fin n => α j = α 0) := by
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [mem_filter, mem_univ, true_and]
      have h1 : α i ≤ α j := hα hj
      have h2 : α j ≤ α 0 := hα (Fin.zero_le j)
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

theorem sum_erase_eq {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ univ.erase i, x j = (∑ j, x j) - x i := by
  rw [← Finset.add_sum_erase _ _ (mem_univ i)]; ring

theorem effort_system {n : ℕ} [NeZero n] (α x : Fin n → ℝ) (hα : Antitone α)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_le_one : ∀ i, α i ≤ 1)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, x i = max (α i - ∑ j ∈ univ.erase i, x j) 0) ↔
      (∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < kbar α), x i = α 0) ∧
      ∀ i : Fin n, kbar α ≤ (i : ℕ) → x i = 0 := by
  set S := ∑ j, x j with hS
  have hsplit : ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < kbar α), x i +
      ∑ i ∈ univ.filter (fun i : Fin n => ¬ (i : ℕ) < kbar α), x i = S :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  constructor
  · intro h
    have h' : ∀ i, x i = max (α i - S + x i) 0 := by
      intro i; have := h i; rw [sum_erase_eq] at this
      rw [show α i - S + x i = α i - (S - x i) by ring]; exact this
    -- S ≥ α i
    have hge : ∀ i, α i ≤ S := by
      intro i; have := le_max_left (α i - S + x i) 0; rw [← h' i] at this; linarith
    -- if α i < S then x i = 0
    have hzero : ∀ i, α i < S → x i = 0 := by
      intro i hi
      rcases le_total (α i - S + x i) 0 with h0 | h0
      · have := h' i; rw [max_eq_right h0] at this; exact this
      · have := h' i; rw [max_eq_left h0] at this; linarith
    have hSeq : S = α 0 := by
      by_contra hne
      have hlt : α 0 < S := lt_of_le_of_ne (hge 0) (Ne.symm hne)
      have hall : ∀ i, x i = 0 := fun i => hzero i (lt_of_le_of_lt (hα (Fin.zero_le i)) hlt)
      have : S = 0 := by rw [hS]; simp [hall]
      linarith [hα_nonneg 0]
    have hz : ∀ i : Fin n, kbar α ≤ (i : ℕ) → x i = 0 := by
      intro i hi
      apply hzero
      have hne : α i ≠ α 0 := fun he => by have := (kbar_iff α hα i).2 he; omega
      have := hα (Fin.zero_le i)
      rw [hSeq]; exact lt_of_le_of_ne this hne
    refine ⟨?_, hz⟩
    have h2 : ∑ i ∈ univ.filter (fun i : Fin n => ¬ (i : ℕ) < kbar α), x i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi
      exact hz i hi
    linarith
  · rintro ⟨h1, h2⟩
    have h2' : ∑ i ∈ univ.filter (fun i : Fin n => ¬ (i : ℕ) < kbar α), x i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [mem_filter, mem_univ, true_and, not_lt] at hi
      exact h2 i hi
    have hSeq : S = α 0 := by linarith
    intro i
    rw [sum_erase_eq, ← hS, hSeq]
    by_cases hi : (i : ℕ) < kbar α
    · have := (kbar_iff α hα i).1 hi
      rw [this, max_eq_left (by linarith [(hx i).1])]; ring
    · push Not at hi
      rw [h2 i hi]
      have := hα (Fin.zero_le i)
      rw [max_eq_right (by linarith)]

end Fundraising.PartialCollab

open Fundraising.PartialCollab Finset in
theorem solution {n : ℕ} [NeZero n] (α x : Fin n → ℝ) (hα : Antitone α)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_le_one : ∀ i, α i ≤ 1)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, x i = max (α i - ∑ j ∈ univ.erase i, x j) 0) ↔
      (∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < kbar α), x i = α 0) ∧
      ∀ i : Fin n, kbar α ≤ (i : ℕ) → x i = 0 :=
  effort_system α x hα hα_nonneg hα_le_one hx
