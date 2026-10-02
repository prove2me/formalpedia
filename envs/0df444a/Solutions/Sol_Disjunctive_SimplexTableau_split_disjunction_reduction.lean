-- Prove2me | solution 1 for Disjunctive.SimplexTableau.split_disjunction_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T21:52:51.186697+00:00
-- url     : https://prove2.me/submissions/6d77b788-0a29-4afe-a5c9-393607da0689

import Mathlib

theorem solution {n : ℕ} (MIP : Set (Fin n → ℝ)) (pi : Fin n → ℤ)
    (pi0 : ℤ) :
    {x ∈ MIP | dotProduct (fun j => (pi j : ℝ)) x ≤ (pi0 : ℝ) ∨
        (pi0 : ℝ) + 1 ≤ dotProduct (fun j => (pi j : ℝ)) x} =
      {x | ∃ y : ℝ, x ∈ MIP ∧ y = dotProduct (fun j => (pi j : ℝ)) x - (pi0 : ℝ) ∧
        (y ≤ 0 ∨ 1 ≤ y)} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_sep_iff]
  constructor
  · rintro ⟨hx, h | h⟩
    · exact ⟨_, hx, rfl, Or.inl (by linarith)⟩
    · exact ⟨_, hx, rfl, Or.inr (by linarith)⟩
  · rintro ⟨y, hx, rfl, h | h⟩
    · exact ⟨hx, Or.inl (by linarith)⟩
    · exact ⟨hx, Or.inr (by linarith)⟩
