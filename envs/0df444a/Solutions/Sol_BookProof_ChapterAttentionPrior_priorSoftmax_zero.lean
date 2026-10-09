-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:35:05.204319+00:00
-- url     : https://prove2.me/submissions/7c08d129-f939-4ba0-8752-b09db667fdc0

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorSoftmax_zero
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin m → ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax w 0 s j = w j / ∑ l, w l := by

  simp [priorSoftmax]
