-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.sinkWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:39:16.883725+00:00
-- url     : https://prove2.me/submissions/90f66d39-8ec8-41d6-94a4-c5e10aeeab58

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.sinkWeight_pos
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Theorems.Thm_BookProof_ChapterAttentionSink_sinkWeight_eq
import Theorems.Thm_BookProof_ChapterAttentionSink_sink_denom_pos
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) : 0 < sinkWeight beta s0 s := by

  rw [sinkWeight_eq]
  exact div_pos (Real.exp_pos _) (sink_denom_pos beta s0 s)
