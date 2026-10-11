-- Prove2me | solution 1 for BookProof.ChapterLogPartitionConvex.convexOn_logPartition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:10.453749+00:00
-- url     : https://prove2.me/submissions/d5441a47-cf8f-4849-9483-4add66243102

-- Generated from ChapterLogPartitionConvex.lean — solution of BookProof.ChapterLogPartitionConvex.convexOn_logPartition
import Mathlib
import Definitions.Def_ChapterLogPartitionConvex
import Theorems.Thm_BookProof_ChapterLogPartitionConvex_deriv_logPartition_eq
import Theorems.Thm_BookProof_ChapterLogPartitionConvex_differentiable_logPartition
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_meanScore_monotone
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterLogPartitionConvex



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (s : Fin m → ℝ) (i : Fin m) :
    ConvexOn ℝ Set.univ fun b : ℝ => logPartition b s := by
  refine Monotone.convexOn_univ_of_deriv (differentiable_logPartition s i) ?_
  rw [deriv_logPartition_eq s i]
  exact meanScore_monotone s i
