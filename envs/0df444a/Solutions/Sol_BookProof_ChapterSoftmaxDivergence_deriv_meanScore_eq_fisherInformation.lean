-- Prove2me | solution 1 for BookProof.ChapterSoftmaxDivergence.deriv_meanScore_eq_fisherInformation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:22:03.938183+00:00
-- url     : https://prove2.me/submissions/50107b20-46f5-4326-9220-340a581947d9

-- Generated from ChapterSoftmaxDivergence.lean — solution of BookProof.ChapterSoftmaxDivergence.deriv_meanScore_eq_fisherInformation
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_deriv_meanScore
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxDivergence



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    deriv (fun b : ℝ => meanScore b s) beta = fisherInformation beta s :=
  deriv_meanScore beta s i
