-- Prove2me | solution 1 for BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:22:02.797843+00:00
-- url     : https://prove2.me/submissions/e50a3a5c-8d8a-4e78-8a46-54a47b7b31cf

-- Generated from ChapterSoftmaxDivergence.lean — solution of BookProof.ChapterSoftmaxDivergence.fisherInformation_eq_varScore
import Mathlib
import Definitions.Def_ChapterSoftmaxDivergence
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

theorem solution (beta : ℝ) (s : Fin m → ℝ) :
    fisherInformation beta s = varScore beta s := rfl
