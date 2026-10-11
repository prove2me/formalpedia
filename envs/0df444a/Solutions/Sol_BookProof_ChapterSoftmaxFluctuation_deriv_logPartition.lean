-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.deriv_logPartition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:46.98718+00:00
-- url     : https://prove2.me/submissions/65173fb2-586b-4d5d-8176-c7bf320fc110

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.deriv_logPartition
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_logPartition
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    deriv (fun b : ℝ => logPartition b s) beta = meanScore beta s := (hasDerivAt_logPartition beta s i).deriv
