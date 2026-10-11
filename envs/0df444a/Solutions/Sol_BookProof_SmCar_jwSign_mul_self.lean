-- Prove2me | solution 1 for BookProof.SmCar.jwSign_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:58.699638+00:00
-- url     : https://prove2.me/submissions/6daf1afb-3b59-49e1-a562-5f9854b92db4

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.jwSign_mul_self
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin n) (S : Finset (Fin n)) : jwSign i S * jwSign i S = 1 := by

  simp [jwSign, ← pow_add, ← two_mul, pow_mul]
