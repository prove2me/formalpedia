-- Prove2me | solution 1 for BookProof.ChapterDutchBook.Coherent.univ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:13.858016+00:00
-- url     : https://prove2.me/submissions/2264c769-b613-4723-9807-fdbf5ea8456f

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.Coherent.univ
import Mathlib
import Definitions.Def_ChapterDutchBook
import Theorems.Thm_BookProof_ChapterDutchBook_payoff_single
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution [Fintype Ω] {Pr : Finset Ω → ℝ} (h : Coherent Pr) :
    Pr (Finset.univ : Finset Ω) = 1 := by

  by_contra hne
  apply h
  refine ⟨1, ![Finset.univ], ![if 1 < Pr Finset.univ then 1 else -1], ?_⟩
  intro ω
  rw [payoff_single]
  have hi : betIndicator (Finset.univ : Finset Ω) ω = 1 := by simp [betIndicator]
  rw [hi]
  rcases lt_trichotomy (Pr Finset.univ) 1 with hlt | heq | hgt
  · rw [if_neg (by linarith)]; simp; linarith
  · exact absurd heq hne
  · rw [if_pos hgt]; simp; linarith
