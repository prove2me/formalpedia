-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.mean_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:26:06.339982+00:00
-- url     : https://prove2.me/submissions/5d9f6aa8-1df2-4042-ab58-baccf4f2af26

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.mean_smul
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterTotalVariance
open BookProof.ChapterLayerNorm



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) (x : Fin d → ℝ) : mean (fun i => a * x i) = a * mean x := by

  simp only [mean, ← Finset.mul_sum]
  ring
