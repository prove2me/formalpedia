-- Prove2me | solution 1 for BookProof.ChapterBayesInference.evidence_eq_marginal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:26:30.750823+00:00
-- url     : https://prove2.me/submissions/8e727442-a963-4744-b8d3-bdf20839c014

-- Generated from ChapterBayesInference.lean — solution of BookProof.ChapterBayesInference.evidence_eq_marginal
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference



open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {prior : X → ℝ} {L : X → Y → ℝ}

set_option maxHeartbeats 1000000 in
omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem solution (y : Y) : evidence prior L y = ∑ x, joint prior L x y := by

  rfl
