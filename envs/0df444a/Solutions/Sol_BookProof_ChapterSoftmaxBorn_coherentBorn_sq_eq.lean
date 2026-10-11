-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:33.606278+00:00
-- url     : https://prove2.me/submissions/7e0b706e-e544-4da3-b3d6-d7917a555dc2

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.coherentBorn_sq_eq
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    bornNumer q k =
      Real.exp (-‖q‖ ^ 2) * Real.exp (-‖k‖ ^ 2) * Real.exp (2 * inner ℝ q k) := by

  rw [bornNumer, coherentOverlap, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
