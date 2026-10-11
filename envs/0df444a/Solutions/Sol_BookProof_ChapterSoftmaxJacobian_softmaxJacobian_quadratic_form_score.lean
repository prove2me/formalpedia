-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:53.571865+00:00
-- url     : https://prove2.me/submissions/67a717a1-6270-43e4-9759-d83d149a5d09

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_quadratic_form_score
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_quadratic_form
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_sub_sq
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ a, ∑ b, s a * softmaxJacobian beta s a b * s b = beta * varScore beta s := by
  rw [softmaxJacobian_quadratic_form]
  simp only [weightedVar, varScore_eq_sub_sq beta s i, meanScore]
