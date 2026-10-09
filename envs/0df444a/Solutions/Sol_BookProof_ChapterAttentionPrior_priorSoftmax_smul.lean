-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:34:30.110384+00:00
-- url     : https://prove2.me/submissions/db8654dc-d72d-49a3-8fc8-0d9334bd7ad9

-- Generated from ChapterAttentionPrior.lean — solution of BookProof.ChapterAttentionPrior.priorSoftmax_smul
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
theorem solution {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {c : ℝ} (hc : 0 < c)
    (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax (fun l => c * w l) beta s j = priorSoftmax w beta s j := by

  have hD : (0 : ℝ) < ∑ l, w l * Real.exp (beta * s l) := priorDenom_pos hw beta s j
  have hsum : ∑ l, c * w l * Real.exp (beta * s l)
      = c * ∑ l, w l * Real.exp (beta * s l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [priorSoftmax, priorSoftmax, hsum]
  field_simp
