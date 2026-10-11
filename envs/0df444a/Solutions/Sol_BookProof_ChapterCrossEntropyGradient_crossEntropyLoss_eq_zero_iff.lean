-- Prove2me | solution 1 for BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:49:06.195838+00:00
-- url     : https://prove2.me/submissions/f00c5f32-05e6-42a7-a1a5-8df76fc6cd80

-- Generated from ChapterCrossEntropyGradient.lean — solution of BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Theorems.Thm_BookProof_ChapterCrossEntropyGradient_crossEntropyLoss_eq_neg_log
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterCrossEntropyGradient



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) :
    crossEntropyLoss beta s y = 0 ↔ scoreSoftmax beta s y = 1 := by

  rw [crossEntropyLoss_eq_neg_log, neg_eq_zero]
  constructor
  · intro h
    have hpos : 0 < scoreSoftmax beta s y := scoreSoftmax_pos beta s y
    rcases Real.log_eq_zero.1 h with h0 | h1 | hm1
    · exact absurd h0 (ne_of_gt hpos)
    · exact h1
    · linarith
  · intro h
    rw [h, Real.log_one]
