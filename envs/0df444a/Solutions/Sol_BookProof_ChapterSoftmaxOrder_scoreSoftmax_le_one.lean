-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:33:43.113166+00:00
-- url     : https://prove2.me/submissions/f2381878-0ce2-4dd4-b25f-467f5df5c7f3

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j ≤ 1 := by

  have hsum := scoreSoftmax_sum_one beta s j
  have hle : scoreSoftmax beta s j ≤ ∑ l, scoreSoftmax beta s l :=
    Finset.single_le_sum (f := fun l => scoreSoftmax beta s l)
      (fun l _ => scoreSoftmax_nonneg beta s l) (Finset.mem_univ j)
  linarith
