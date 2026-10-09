-- Prove2me | solution 1 for BookProof.ChapterDutchBook.Coherent.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:11.665391+00:00
-- url     : https://prove2.me/submissions/1da022e7-d675-47e8-9293-c88aca244d11

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.Coherent.nonneg
import Mathlib
import Definitions.Def_ChapterDutchBook
import Theorems.Thm_BookProof_ChapterDutchBook_payoff_single
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution {Pr : Finset Ω → ℝ} (h : Coherent Pr) (A : Finset Ω) :
    0 ≤ Pr A := by

  by_contra hlt
  push_neg at hlt
  apply h
  refine ⟨1, ![A], ![-1], ?_⟩
  intro ω
  rw [payoff_single]
  have hcases : betIndicator A ω = 0 ∨ betIndicator A ω = 1 := by
    unfold betIndicator; split <;> simp
  rcases hcases with h0 | h1
  · rw [h0]; simp; linarith
  · rw [h1]; simp; linarith
