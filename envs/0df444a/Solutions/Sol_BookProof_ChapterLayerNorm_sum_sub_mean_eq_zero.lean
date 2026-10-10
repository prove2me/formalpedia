-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.sum_sub_mean_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:22:42.173058+00:00
-- url     : https://prove2.me/submissions/f94bac68-1cb7-48ce-910a-b3ebbe729679

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.sum_sub_mean_eq_zero
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
theorem solution (hd : 0 < d) (x : Fin d → ℝ) : ∑ i, (x i - mean x) = 0 := by

  have hd' : (d : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  ring
