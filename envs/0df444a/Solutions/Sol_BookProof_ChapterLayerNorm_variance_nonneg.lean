-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.variance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:23:15.465+00:00
-- url     : https://prove2.me/submissions/3cb4f29a-9077-4a2a-9370-9e31df3f21d6

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.variance_nonneg
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
theorem solution (x : Fin d → ℝ) : 0 ≤ variance x := by

  refine div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Nat.cast_nonneg d)
