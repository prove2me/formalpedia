-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:40:07.108803+00:00
-- url     : https://prove2.me/submissions/7e5dc790-60fd-4bbf-ae14-5c0947b43b05

-- Generated from ChapterAttentionSink.lean — solution of BookProof.ChapterAttentionSink.scoreSoftmax_sink_odds
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Theorems.Thm_BookProof_ChapterAttentionSink_scoreSoftmax_sink_succ
open BookProof.ChapterAttentionSink



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta s0 : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta (Fin.cons s0 s) i.succ * scoreSoftmax beta s j
      = scoreSoftmax beta (Fin.cons s0 s) j.succ * scoreSoftmax beta s i := by

  rw [scoreSoftmax_sink_succ, scoreSoftmax_sink_succ]
  ring
