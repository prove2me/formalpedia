-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:33:31.483507+00:00
-- url     : https://prove2.me/submissions/678de688-fa4e-436c-9211-344e240dc887

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorSoftmax_pos
import Mathlib
import Definitions.Def_ChapterAttentionPrior
import Theorems.Thm_BookProof_ChapterAttentionPrior_priorDenom_pos
open BookProof.ChapterAttentionPrior



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) (beta : ℝ) (s : Fin m → ℝ)
    (j : Fin m) : 0 < priorSoftmax w beta s j := div_pos (mul_pos (hw j) (Real.exp_pos _)) (priorDenom_pos hw beta s j)
