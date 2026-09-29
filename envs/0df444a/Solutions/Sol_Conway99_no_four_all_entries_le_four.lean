-- Prove2me | solution 1 for Conway99.no_four_all_entries_le_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-08T01:01:52.825485+00:00
-- url     : https://prove2.me/submissions/fbfb919c-6729-48aa-a9c5-a9ef8f4c31d3

import Mathlib
import Theorems.Thm_Conway99_diag_two_offdiag_profile
import Theorems.Thm_Conway99_diag_zero_offdiag_profile

open scoped BigOperators
open Conway99

theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (hfour : ∀ i, C i i ≠ 4) :
    ∀ i j, C i j ≤ 4 := by
  intro i j
  rcases hdiag i with hi0 | hi2 | hi4
  · -- Diagonal-0 row: profile census gives four cases, each with no 5s.
    have hprof := diag_zero_offdiag_profile C hsymm hrow hsq i hi0
    have hsqsum : ∑ k, C i k ^ 2 = 34 := by
      have h := hsq i i
      rw [if_pos rfl] at h
      have hsum : (∑ k, C i k * C k i) = ∑ k, C i k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hsymm i k, pow_two]
      rw [hsum, hi0] at h
      omega
    have hle5 : C i j ≤ 5 := by
      by_contra hgt
      push Not at hgt
      have h6 : 6 ≤ C i j := hgt
      have h36 : 36 ≤ C i j ^ 2 := by
        have hmul := Nat.mul_le_mul h6 h6
        calc (36 : ℕ) = 6 * 6 := by omega
          _ ≤ C i j * C i j := hmul
          _ = C i j ^ 2 := by rw [pow_two]
      have hle : C i j ^ 2 ≤ ∑ k, C i k ^ 2 :=
        Finset.single_le_sum (f := fun k => C i k ^ 2) (fun k hk => Nat.zero_le _) (Finset.mem_univ j)
      omega
    by_cases hji : j = i
    · subst hji; omega
    · have hmem : j ∈ Finset.univ.erase i := by simp [hji]
      have hne5 : C i j ≠ 5 := by
        intro h5
        have hmem5 : j ∈ (Finset.univ.erase i).filter (fun k => C i k = 5) := by
          simp [hmem, h5]
        have hpos : 0 < ((Finset.univ.erase i).filter (fun k => C i k = 5)).card :=
          Finset.card_pos.mpr ⟨j, hmem5⟩
        rcases hprof with h | h | h | h <;> omega
      omega
  · -- Diagonal-2 row: profile census gives two cases, each with no 5s.
    have hprof := diag_two_offdiag_profile C hsymm hrow hsq i hi2
    have hsqsum : ∑ k, C i k ^ 2 = 32 := by
      have h := hsq i i
      rw [if_pos rfl] at h
      have hsum : (∑ k, C i k * C k i) = ∑ k, C i k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hsymm i k, pow_two]
      rw [hsum, hi2] at h
      omega
    have hle5 : C i j ≤ 5 := by
      by_contra hgt
      push Not at hgt
      have h6 : 6 ≤ C i j := hgt
      have h36 : 36 ≤ C i j ^ 2 := by
        have hmul := Nat.mul_le_mul h6 h6
        calc (36 : ℕ) = 6 * 6 := by omega
          _ ≤ C i j * C i j := hmul
          _ = C i j ^ 2 := by rw [pow_two]
      have hle : C i j ^ 2 ≤ ∑ k, C i k ^ 2 :=
        Finset.single_le_sum (f := fun k => C i k ^ 2) (fun k hk => Nat.zero_le _) (Finset.mem_univ j)
      omega
    by_cases hji : j = i
    · subst hji; omega
    · have hmem : j ∈ Finset.univ.erase i := by simp [hji]
      have hne5 : C i j ≠ 5 := by
        intro h5
        have hmem5 : j ∈ (Finset.univ.erase i).filter (fun k => C i k = 5) := by
          simp [hmem, h5]
        have hpos : 0 < ((Finset.univ.erase i).filter (fun k => C i k = 5)).card :=
          Finset.card_pos.mpr ⟨j, hmem5⟩
        rcases hprof with h | h <;> omega
      omega
  · exact absurd hi4 (hfour i)
