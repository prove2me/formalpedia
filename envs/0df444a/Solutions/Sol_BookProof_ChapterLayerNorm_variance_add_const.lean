-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.variance_add_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:25:40.982187+00:00
-- url     : https://prove2.me/submissions/4b3c86ee-4031-4931-a935-aec10a96cc18

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.variance_add_const
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Theorems.Thm_BookProof_ChapterLayerNorm_mean_add_const
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
theorem solution (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) :
    variance (fun i => x i + c) = variance x := by

  simp only [variance, mean_add_const hd x c]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring_nf
