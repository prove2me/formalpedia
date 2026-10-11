-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:08.333324+00:00
-- url     : https://prove2.me/submissions/79be35b2-acf1-45bf-8d6c-528a4ab35a7b

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_offDiag_nonpos
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    {i j : Fin m} (hij : j ≠ i) : softmaxJacobian beta s i j ≤ 0 := by

  have h2 : 0 ≤ scoreSoftmax beta s i := le_of_lt (scoreSoftmax_pos beta s i)
  have h3 : 0 ≤ scoreSoftmax beta s j := le_of_lt (scoreSoftmax_pos beta s j)
  have : softmaxJacobian beta s i j
      = -(beta * scoreSoftmax beta s j * scoreSoftmax beta s i) := by
    simp only [softmaxJacobian, hij, if_false]
    ring
  rw [this, neg_nonpos]
  exact mul_nonneg (mul_nonneg hb h3) h2
