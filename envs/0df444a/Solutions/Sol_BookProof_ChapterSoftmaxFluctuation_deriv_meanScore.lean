-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.deriv_meanScore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:51.844791+00:00
-- url     : https://prove2.me/submissions/5511e2a8-fca3-4daa-ab2d-d1e3938631a4

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.deriv_meanScore
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_meanScore
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
    deriv (fun b : ℝ => meanScore b s) beta = varScore beta s := (hasDerivAt_meanScore beta s i).deriv
