-- Prove2me | solution 1 for BookProof.SmCar.inner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:53.486959+00:00
-- url     : https://prove2.me/submissions/4c0ec1c6-6405-4b5b-8147-a7bda0531ca2

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.inner_eq_sum
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (x y : FermiFock n) :
    (inner ℂ x y : ℂ) = ∑ S : Finset (Fin n), (starRingEnd ℂ) (x S) * y S := by

  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
