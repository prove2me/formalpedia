-- Prove2me | solution 1 for BookProof.ChapterBayesInference.evidence_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:26:31.925599+00:00
-- url     : https://prove2.me/submissions/bea575f0-3653-42ae-8752-7c558f346ce8

-- Generated from ChapterBayesInference.lean — solution of BookProof.ChapterBayesInference.evidence_nonneg
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference



open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {prior : X → ℝ} {L : X → Y → ℝ}

set_option maxHeartbeats 1000000 in
omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem solution (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) :
    0 ≤ evidence prior L y := by

  exact Finset.sum_nonneg fun x _ => mul_nonneg ( hprior x ) ( hL x y )
