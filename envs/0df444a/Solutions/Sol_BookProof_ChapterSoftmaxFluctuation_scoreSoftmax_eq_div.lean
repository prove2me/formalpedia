-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:22:33.389418+00:00
-- url     : https://prove2.me/submissions/41526a9e-3b82-4760-ba9a-6798c2af91a2

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.scoreSoftmax_eq_div
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j = Real.exp (beta * s j) / partition beta s := rfl
