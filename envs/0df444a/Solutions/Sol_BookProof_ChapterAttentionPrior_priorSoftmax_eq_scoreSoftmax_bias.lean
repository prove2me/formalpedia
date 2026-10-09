-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:34:28.900304+00:00
-- url     : https://prove2.me/submissions/7f298b93-64b7-4c10-b010-eca30f614060

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorSoftmax_eq_scoreSoftmax_bias
import Mathlib
import Definitions.Def_ChapterAttentionPrior
open BookProof.ChapterAttentionPrior



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin m → ℝ} (hw : ∀ j, 0 < w j)
    {beta : ℝ} (hb : beta ≠ 0) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax w beta s j
      = scoreSoftmax beta (fun l => s l + Real.log (w l) / beta) j := by

  have hterm : ∀ l : Fin m,
      Real.exp (beta * (s l + Real.log (w l) / beta)) = w l * Real.exp (beta * s l) := by
    intro l
    rw [mul_add, Real.exp_add, mul_div_cancel₀ _ hb, Real.exp_log (hw l), mul_comm]
  rw [scoreSoftmax, priorSoftmax, hterm j]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => (hterm l).symm)
