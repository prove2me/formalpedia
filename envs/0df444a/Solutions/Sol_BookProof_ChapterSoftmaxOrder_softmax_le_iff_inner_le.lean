-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:37.218815+00:00
-- url     : https://prove2.me/submissions/46ba9b5d-20a0-4c0e-b59a-421be49b3e7a

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_le_iff
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_eq_scoreSoftmax
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} {beta : ℝ} (hbeta : 0 < beta)
    (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) :
    softmax beta q k i ≤ softmax beta q k j ↔
      (inner ℝ q (k i) : ℝ) ≤ inner ℝ q (k j) := by

  rw [softmax_eq_scoreSoftmax, softmax_eq_scoreSoftmax, scoreSoftmax_le_iff hbeta]
