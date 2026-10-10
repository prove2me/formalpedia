-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.layerNorm_layerNorm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:27:14.773337+00:00
-- url     : https://prove2.me/submissions/53468fad-5080-43fe-ad4d-49354edf3d12

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.layerNorm_layerNorm
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Theorems.Thm_BookProof_ChapterLayerNorm_mean_layerNorm
import Theorems.Thm_BookProof_ChapterLayerNorm_variance_layerNorm
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
theorem solution (hd : 0 < d) {x : Fin d → ℝ} (hx : 0 < variance x) (i : Fin d) :
    layerNorm (layerNorm x) i = layerNorm x i := by

  rw [layerNorm, mean_layerNorm hd x, variance_layerNorm hd hx]
  simp
