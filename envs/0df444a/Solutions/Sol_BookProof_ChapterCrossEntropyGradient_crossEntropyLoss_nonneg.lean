-- Prove2me | solution 1 for BookProof.ChapterCrossEntropyGradient.crossEntropyLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:34:35.41598+00:00
-- url     : https://prove2.me/submissions/ab65ef2c-1f25-4312-baa6-2d7365935264

import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterCrossEntropyGradient
import Definitions.Def_ChapterSoftmaxSharpness

open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterCrossEntropyGradient BookProof.ChapterSoftmaxFluctuation

theorem solution {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) :
    0 ≤ crossEntropyLoss beta s y := by
  unfold crossEntropyLoss logPartition partition
  have hle : Real.exp (beta * s y) ≤ ∑ l, Real.exp (beta * s l) :=
    Finset.single_le_sum (f := fun l => Real.exp (beta * s l))
      (fun l _ => (Real.exp_pos _).le) (Finset.mem_univ y)
  have hlog := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp] at hlog
  linarith
