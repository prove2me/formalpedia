-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.bornProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:46.017632+00:00
-- url     : https://prove2.me/submissions/d124b2fd-8b82-4214-b0e4-c93e2c9aec3b

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.bornProb_nonneg
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin m → EuclideanSpace ℂ (Fin n))
    (q : EuclideanSpace ℂ (Fin n)) (j : Fin m) : 0 ≤ bornProb k q j := sq_nonneg _
