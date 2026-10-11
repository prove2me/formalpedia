-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:36.158486+00:00
-- url     : https://prove2.me/submissions/a70cea6b-2032-4803-9541-b82ee838f12b

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_const
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta c : ℝ) (j : Fin m) :
    scoreSoftmax beta (fun _ => c) j = 1 / m := by

  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos j).ne'
  simp only [scoreSoftmax, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
