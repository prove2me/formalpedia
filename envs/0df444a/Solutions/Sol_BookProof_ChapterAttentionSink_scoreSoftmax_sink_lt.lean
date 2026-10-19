-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.scoreSoftmax_sink_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:40:17.259355+00:00
-- url     : https://prove2.me/submissions/8a73a903-25e1-4aa0-81e9-675ea14d4221

import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.scoreSoftmax_sink_lt
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (Fin.cons s0 s) j.succ < scoreSoftmax beta s j := by
  unfold scoreSoftmax
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_succ, Fin.cons_zero]
  have hS : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩
  apply div_lt_div_of_pos_left (Real.exp_pos _) hS
  linarith [Real.exp_pos (beta * s0)]
