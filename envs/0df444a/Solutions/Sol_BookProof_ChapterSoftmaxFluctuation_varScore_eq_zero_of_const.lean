-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:56.029884+00:00
-- url     : https://prove2.me/submissions/53e99721-70e6-47d5-b54c-acd80c659cd3

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.varScore_eq_zero_of_const
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_zero_iff
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c)
    (beta : ℝ) (i : Fin m) : varScore beta s = 0 := by

  refine (varScore_eq_zero_iff beta s).2 fun l => ?_
  have hmean : meanScore beta s = c := by
    rw [meanScore, Finset.sum_congr rfl fun j _ => by rw [hs j], ← Finset.sum_mul,
      scoreSoftmax_sum_one beta s i, one_mul]
  rw [hs l, hmean]
