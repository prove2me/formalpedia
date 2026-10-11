-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:56.948156+00:00
-- url     : https://prove2.me/submissions/b65f971c-047f-4ec1-8ef3-6f560a5519a8

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.varScore_pos_of_ne
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_varScore_eq_zero_iff
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} {s : Fin m → ℝ} {a b : Fin m} (hab : s a ≠ s b) :
    0 < varScore beta s := by

  rcases lt_or_eq_of_le (varScore_nonneg beta s) with h | h
  · exact h
  · exfalso
    have hall := (varScore_eq_zero_iff beta s).1 h.symm
    exact hab ((hall a).trans (hall b).symm)
