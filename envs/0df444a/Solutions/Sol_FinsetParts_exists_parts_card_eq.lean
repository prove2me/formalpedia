-- Prove2me | solution 1 for FinsetParts.exists_parts_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T18:24:43.526102+00:00
-- url     : https://prove2.me/submissions/39772725-6cee-41c7-b33e-c4f1b4b76152

import Mathlib

open Finset
namespace FinsetParts

/-- Splitting a finite set into parts of prescribed sizes: if `b₁ + ⋯ + bₙ = |X|`, then `X` is the disjoint union of subsets `Y₁, …, Yₙ` with `|Yᵢ| = bᵢ`. -/
theorem exists_parts_card_eq {α : Type*} [DecidableEq α] {n : ℕ} (X : Finset α)
    (b : Fin n → ℕ) (h : ∑ i, b i = X.card) :
    ∃ Y : Fin n → Finset α, (∀ i, Y i ⊆ X) ∧ (∀ i, (Y i).card = b i) ∧
      ∀ x ∈ X, ∃! i, x ∈ Y i := by
  induction n generalizing X with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    simp at h
    intro x hx
    rw [Finset.card_eq_zero.mp h.symm] at hx
    simp at hx
  | succ n ih =>
    rw [Fin.sum_univ_succ] at h
    obtain ⟨Y0, hY0X, hY0c⟩ := Finset.exists_subset_card_eq (show b 0 ≤ X.card by omega)
    obtain ⟨Y', hY'X, hY'c, hY'u⟩ := ih (X \ Y0) (fun i => b i.succ)
      (by rw [Finset.card_sdiff_of_subset hY0X]; omega)
    refine ⟨Fin.cons Y0 Y', ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hY0X
      · simpa using (hY'X j).trans Finset.sdiff_subset
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hY0c
      · simpa using hY'c j
    · intro x hx
      by_cases h0 : x ∈ Y0
      · refine ⟨0, by simpa using h0, fun j hj => ?_⟩
        revert hj
        refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
        simp only [Fin.cons_succ] at hj
        have := hY'X j hj
        simp [h0] at this
      · obtain ⟨j, hj, hju⟩ := hY'u x (by simp [hx, h0])
        refine ⟨j.succ, by simpa using hj, fun i hi => ?_⟩
        revert hi
        refine Fin.cases (fun hi => ?_) (fun i hi => ?_) i
        · simp at hi; exact absurd hi h0
        · simp only [Fin.cons_succ] at hi
          rw [hju i hi]

end FinsetParts

open FinsetParts in
theorem solution {α : Type*} [DecidableEq α] {n : ℕ} (X : Finset α)
    (b : Fin n → ℕ) (h : ∑ i, b i = X.card) :
    ∃ Y : Fin n → Finset α, (∀ i, Y i ⊆ X) ∧ (∀ i, (Y i).card = b i) ∧
      ∀ x ∈ X, ∃! i, x ∈ Y i :=
  FinsetParts.exists_parts_card_eq X b h
