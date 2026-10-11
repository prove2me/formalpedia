-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.partition_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:22:19.529678+00:00
-- url     : https://prove2.me/submissions/5d867f13-630d-4c13-87d3-045d6db87c5c

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.partition_ne_zero
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_partition_pos
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : partition beta s ≠ 0 := ne_of_gt (partition_pos beta s i)
