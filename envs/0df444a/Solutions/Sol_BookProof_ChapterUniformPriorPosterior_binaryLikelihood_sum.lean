-- Prove2me | solution 1 for BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:14:37.018004+00:00
-- url     : https://prove2.me/submissions/07298b47-afd2-42c3-8173-b2bacb90a67a

-- Generated from ChapterUniformPriorPosterior.lean — solution of BookProof.ChapterUniformPriorPosterior.binaryLikelihood_sum
import Mathlib
import Definitions.Def_ChapterUniformPriorPosterior
open BookProof.ChapterUniformPriorPosterior



open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

variable {Hyp : Type*} [Fintype Hyp] [DecidableEq Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (q : Hyp → ℝ) (x : Hyp) :
    ∑ observed : Bool, binaryLikelihood q x observed = 1 := by

  simp [binaryLikelihood]
