-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:44:56.504861+00:00
-- url     : https://prove2.me/submissions/c476d8d5-ac2c-4e0d-ac3e-2942c0fc552f

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_deriv_scoreSoftmax_beta
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_min_le_meanScore
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_differentiable_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxTemperatureMonotone



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) :
    Antitone fun b : ℝ => scoreSoftmax b s i := by
  refine antitone_of_deriv_nonpos (differentiable_scoreSoftmax s i) fun b => ?_
  rw [deriv_scoreSoftmax_beta b s i]
  have hmean : s i ≤ meanScore b s := min_le_meanScore b s i hmin
  exact mul_nonpos_of_nonneg_of_nonpos (scoreSoftmax_nonneg b s i) (by linarith)

/-! ## Comparing two temperatures -/
