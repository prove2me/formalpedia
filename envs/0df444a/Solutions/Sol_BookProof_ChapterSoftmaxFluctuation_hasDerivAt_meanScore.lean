-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:50.948122+00:00
-- url     : https://prove2.me/submissions/f39671a9-ad71-43ca-a8c3-dcfcf0b3b5d5

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.hasDerivAt_meanScore
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_sub_sq
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
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun b : ℝ => meanScore b s) (varScore beta s) beta := by

  have h : HasDerivAt (fun b : ℝ => ∑ l, scoreSoftmax b s l * s l)
      (∑ l, scoreSoftmax beta s l * (s l - meanScore beta s) * s l) beta :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_scoreSoftmax beta s l).mul_const (s l)
  refine h.congr_deriv ?_
  rw [varScore_eq_sub_sq beta s i]
  have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s i
  have hexp : ∀ l : Fin m, scoreSoftmax beta s l * (s l - meanScore beta s) * s l
      = scoreSoftmax beta s l * s l ^ 2
        - meanScore beta s * (scoreSoftmax beta s l * s l) := by
    intro l; ring
  rw [Finset.sum_congr rfl fun l _ => hexp l, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← meanScore]
  ring
