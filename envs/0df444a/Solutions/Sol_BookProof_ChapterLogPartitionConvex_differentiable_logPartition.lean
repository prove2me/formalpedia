-- Prove2me | solution 1 for BookProof.ChapterLogPartitionConvex.differentiable_logPartition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:08.059933+00:00
-- url     : https://prove2.me/submissions/882542d7-2645-4acf-8bc0-b1d4cf275605

-- Generated from ChapterLogPartitionConvex.lean — solution of BookProof.ChapterLogPartitionConvex.differentiable_logPartition
import Mathlib
import Definitions.Def_ChapterLogPartitionConvex
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_logPartition
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
    Differentiable ℝ fun b : ℝ => logPartition b s := fun b =>
  (hasDerivAt_logPartition b s i).differentiableAt
