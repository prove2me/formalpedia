-- Prove2me | solution 1 for BookProof.ChapterDutchBook.Coherent.le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:12.827042+00:00
-- url     : https://prove2.me/submissions/c9b5da00-7159-4292-82f8-708a7983c29c

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.Coherent.le_one
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
    Pr A ≤ 1 := by

  by_contra hlt
  push_neg at hlt
  apply h
  refine ⟨1, ![A], ![1], ?_⟩
  intro ω
  rw [payoff_single]
  have hcases : betIndicator A ω = 0 ∨ betIndicator A ω = 1 := by
    unfold betIndicator; split <;> simp
  rcases hcases with h0 | h1
  · rw [h0]; simp; linarith
  · rw [h1]; simp; linarith
