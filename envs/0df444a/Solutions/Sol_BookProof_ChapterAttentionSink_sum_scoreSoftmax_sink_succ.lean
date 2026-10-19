-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:40:00.655991+00:00
-- url     : https://prove2.me/submissions/99717767-e369-41c3-9988-d1b1b39cbcc6

import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.sum_scoreSoftmax_sink_succ
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j : Fin m, scoreSoftmax beta (Fin.cons s0 s) j.succ = 1 - sinkWeight beta s0 s := by
  have hsum : ∑ j : Fin (m + 1), scoreSoftmax beta (Fin.cons s0 s : Fin (m + 1) → ℝ) j = 1 := by
    unfold scoreSoftmax
    rw [← Finset.sum_div, div_self]
    exact (Finset.sum_pos (fun l _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  rw [Fin.sum_univ_succ] at hsum
  unfold sinkWeight
  linarith
