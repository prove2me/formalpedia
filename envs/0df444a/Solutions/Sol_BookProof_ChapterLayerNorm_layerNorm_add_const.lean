-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.layerNorm_add_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:25:54.019096+00:00
-- url     : https://prove2.me/submissions/d44c46a8-4472-4d4d-b3d7-29814223b780

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.layerNorm_add_const
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Theorems.Thm_BookProof_ChapterLayerNorm_mean_add_const
import Theorems.Thm_BookProof_ChapterLayerNorm_variance_add_const
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
theorem solution (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) (i : Fin d) :
    layerNorm (fun i => x i + c) i = layerNorm x i := by

  simp only [layerNorm, variance_add_const hd x c, mean_add_const hd x c]
  ring_nf
