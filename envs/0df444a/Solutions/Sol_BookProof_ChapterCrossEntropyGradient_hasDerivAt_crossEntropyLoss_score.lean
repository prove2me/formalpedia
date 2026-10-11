-- Prove2me | solution 1 for BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:49:07.228814+00:00
-- url     : https://prove2.me/submissions/9359e914-179d-4630-8a53-c61d3ef9ba2e

-- Generated from ChapterCrossEntropyGradient.lean — solution of BookProof.ChapterCrossEntropyGradient.hasDerivAt_crossEntropyLoss_score
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_logPartition_score
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_scorePerturb_of_ne
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian
open BookProof.ChapterCrossEntropyGradient



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (y i : Fin m) :
    HasDerivAt (fun t : ℝ => crossEntropyLoss beta (scorePerturb s i t) y)
      (crossEntropyGradient beta s y i) 0 := by

  have hlog := hasDerivAt_logPartition_score beta s i
  have henergy : HasDerivAt (fun t : ℝ => beta * scorePerturb s i t y)
      (beta * (if i = y then 1 else 0)) 0 := by
    by_cases h : y = i
    · subst h
      have : HasDerivAt (fun t : ℝ => beta * (s y + t)) beta 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add (s y)).const_mul beta
      simpa [scorePerturb, mul_comm] using this
    · have hconst : (fun t : ℝ => beta * scorePerturb s i t y)
          = fun _ : ℝ => beta * s y := by
        funext t
        rw [scorePerturb_of_ne s h t]
      have hiy : (if i = y then (1 : ℝ) else 0) = 0 := if_neg fun hh => h hh.symm
      rw [hconst, hiy, mul_zero]
      exact hasDerivAt_const (0 : ℝ) (beta * s y)
  have h := hlog.sub henergy
  refine h.congr_deriv ?_
  rw [crossEntropyGradient]
  ring
