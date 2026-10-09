-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_odds
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:34:16.975353+00:00
-- url     : https://prove2.me/submissions/4c0810f8-0207-43b1-b0f3-5e0f2e4bc743

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorSoftmax_odds
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
    (i j : Fin m) :
    priorSoftmax w beta s i
      = (w i / w j) * Real.exp (beta * (s i - s j)) * priorSoftmax w beta s j := by

  have hD : (0 : ℝ) < ∑ l, w l * Real.exp (beta * s l) := priorDenom_pos hw beta s i
  have hwj : w j ≠ 0 := (hw j).ne'
  rw [priorSoftmax, priorSoftmax, mul_sub, Real.exp_sub]
  field_simp
