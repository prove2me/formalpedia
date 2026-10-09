-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.sinkWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:38:15.577743+00:00
-- url     : https://prove2.me/submissions/64666b2a-00f3-448b-bf12-5c72f88322b8

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.sinkWeight_eq
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Theorems.Thm_BookProof_ChapterAttentionSink_sink_denom
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) :
    sinkWeight beta s0 s
      = Real.exp (beta * s0) / (Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l)) := by

  rw [sinkWeight, scoreSoftmax, sink_denom]
  simp
