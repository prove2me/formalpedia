-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:07.404094+00:00
-- url     : https://prove2.me/submissions/54e3594d-2c32-4b0a-8100-6c843f0087fc

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_diag_nonneg
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_le_one
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
theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m) :
    0 ≤ softmaxJacobian beta s i i := by

  have h1 : scoreSoftmax beta s i ≤ 1 := scoreSoftmax_le_one beta s i
  have h2 : 0 ≤ scoreSoftmax beta s i := le_of_lt (scoreSoftmax_pos beta s i)
  have : 0 ≤ (1 : ℝ) - scoreSoftmax beta s i := by linarith
  simpa [softmaxJacobian] using mul_nonneg (mul_nonneg hb h2) this
