-- Prove2me | solution 1 for BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:42:49.255613+00:00
-- url     : https://prove2.me/submissions/2e727cc1-5da0-421b-8800-6a68e659faac

-- Generated from ChapterNoBestPrior.lean — solution of BookProof.ChapterNoBestPrior.eq_of_expectedUtility_ge_all
import Mathlib
import Definitions.Def_ChapterNoBestPrior
open BookProof.ChapterNoBestPrior



open scoped BigOperators


variable {Hyp : Type*} [Fintype Hyp]

variable {Hyp : Type*} [Fintype Hyp]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Hyp → ℝ)
    (h : ∀ u : Hyp → ℝ, expectedUtility q u ≤ expectedUtility p u) :
    p = q := by

  classical
  unfold expectedUtility at h
  ext x
  exact le_antisymm
    (by simpa using h (fun y => if y = x then -1 else 0))
    (by simpa using h (fun y => if y = x then 1 else 0))
