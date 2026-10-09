-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_uniform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:34:31.163149+00:00
-- url     : https://prove2.me/submissions/dda7fc92-c147-49aa-8370-60c8e73c8ccf

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorSoftmax_uniform
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {c : ℝ} (hc : 0 < c) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax (fun _ => c) beta s j = scoreSoftmax beta s j := by

  have hsum : ∑ l, c * Real.exp (beta * s l) = c * ∑ l, Real.exp (beta * s l) := by
    rw [Finset.mul_sum]
  rw [priorSoftmax, scoreSoftmax, hsum, mul_div_mul_left _ _ hc.ne']
