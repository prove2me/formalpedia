-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:06.483047+00:00
-- url     : https://prove2.me/submissions/47433b6b-aa84-4772-bbee-8cfc3671bd28

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_row_sum_zero
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j, softmaxJacobian beta s i j = 0 := by

  have hsum : ∑ j, scoreSoftmax beta s j = 1 := scoreSoftmax_sum_one beta s i
  have hterm : ∀ j : Fin m, softmaxJacobian beta s i j
      = (if j = i then beta * scoreSoftmax beta s j else 0)
        - beta * scoreSoftmax beta s i * scoreSoftmax beta s j := by
    intro j
    rcases eq_or_ne j i with hj | hj
    · subst hj
      rw [softmaxJacobian, if_pos (rfl : j = j), if_pos (rfl : j = j)]
      ring
    · rw [softmaxJacobian, if_neg hj, if_neg hj]
      ring
  have hpick : ∑ j, (if j = i then beta * scoreSoftmax beta s j else 0)
      = beta * scoreSoftmax beta s i :=
    by simp
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, hpick,
    ← Finset.mul_sum, hsum]
  ring
