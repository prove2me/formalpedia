-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:45.080563+00:00
-- url     : https://prove2.me/submissions/78eb2d59-d9e4-41cf-82a0-fc79d81620fb

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.hasDerivAt_partition
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_exp_mul
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) :
    HasDerivAt (fun b : ℝ => partition b s)
      (∑ l, s l * Real.exp (beta * s l)) beta := HasDerivAt.fun_sum fun l _ => hasDerivAt_exp_mul beta (s l)
