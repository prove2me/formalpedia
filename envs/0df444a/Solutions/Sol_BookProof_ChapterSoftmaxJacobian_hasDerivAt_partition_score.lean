-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:30:01.533563+00:00
-- url     : https://prove2.me/submissions/e81ddf0b-c445-455b-bbe9-9ff2bcbfb452

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.hasDerivAt_partition_score
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_exp_score
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => partition beta (scorePerturb s i t))
      (beta * Real.exp (beta * s i)) 0 := by
  have h : HasDerivAt (fun t : ℝ => ∑ l, Real.exp (beta * scorePerturb s i t l))
      (∑ l, if l = i then beta * Real.exp (beta * s i) else 0) 0 := by
    refine HasDerivAt.fun_sum fun l _ => ?_
    by_cases hl : l = i
    · subst hl
      simpa [scorePerturb] using hasDerivAt_exp_score beta 0 (s l)
    · simpa [scorePerturb, hl] using
        (hasDerivAt_const (0 : ℝ) (Real.exp (beta * s l)))
  simpa [partition] using h
