-- Prove2me | solution 1 for BookProof.SmCar.normSq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:57.370225+00:00
-- url     : https://prove2.me/submissions/930c140a-0b37-4842-a26f-a73f5b986ca8

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.normSq_eq_sum
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (x : FermiFock n) :
    ‖x‖ ^ 2 = ∑ S : Finset (Fin n), ‖x S‖ ^ 2 := by

  rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
  exact Finset.sum_nonneg fun S _ => by positivity
