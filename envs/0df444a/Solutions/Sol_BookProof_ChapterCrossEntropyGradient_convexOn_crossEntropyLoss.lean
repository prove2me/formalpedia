-- Prove2me | solution 1 for BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:55:54.126005+00:00
-- url     : https://prove2.me/submissions/cefe70b4-8d4a-42da-a6b4-2f1e109a2c4f

import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Theorems.Thm_BookProof_ChapterLogPartitionConvex_convexOn_logPartition
-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.convexOn_crossEntropyLoss
open BookProof.ChapterCrossEntropyGradient


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}


theorem solution (s : Fin m → ℝ) (y : Fin m) :
    ConvexOn ℝ Set.univ (fun b : ℝ => crossEntropyLoss b s y) := by
  have h := BookProof.ChapterLogPartitionConvex.convexOn_logPartition s y
  refine ⟨convex_univ, fun a _ b _ u v hu hv huv => ?_⟩
  have := h.2 (Set.mem_univ a) (Set.mem_univ b) hu hv huv
  simp only [smul_eq_mul] at this ⊢
  unfold crossEntropyLoss
  have e : (u * a + v * b) * s y = u * (a * s y) + v * (b * s y) := by ring
  rw [e]
  nlinarith [this]

