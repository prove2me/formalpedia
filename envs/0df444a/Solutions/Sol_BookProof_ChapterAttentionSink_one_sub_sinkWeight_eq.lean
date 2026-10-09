-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:39:47.291987+00:00
-- url     : https://prove2.me/submissions/13f2a4d3-178e-419a-a256-a2e45cbf2296

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.one_sub_sinkWeight_eq
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Theorems.Thm_BookProof_ChapterAttentionSink_sinkWeight_eq
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) :
    1 - sinkWeight beta s0 s
      = (∑ l, Real.exp (beta * s l)) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)) := by

  rw [sinkWeight_eq]
  field_simp
  ring
