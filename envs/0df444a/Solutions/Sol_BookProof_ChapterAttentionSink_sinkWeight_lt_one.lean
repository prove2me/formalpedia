-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.sinkWeight_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:39:42.929369+00:00
-- url     : https://prove2.me/submissions/e7c1a0c7-0d3f-40eb-99c0-ef9fe9fb7f46

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.sinkWeight_lt_one
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
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    sinkWeight beta s0 s < 1 := by

  have hZ : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  rw [sinkWeight_eq, div_lt_one (sink_denom_pos beta s0 s)]
  linarith
