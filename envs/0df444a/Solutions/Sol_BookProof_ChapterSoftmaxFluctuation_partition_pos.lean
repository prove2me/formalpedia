-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.partition_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:22:04.950197+00:00
-- url     : https://prove2.me/submissions/67cbcf80-2b77-4915-8c96-8c396e0939d9

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.partition_pos
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : 0 < partition beta s := scoreSoftmax_denom_pos beta s i
