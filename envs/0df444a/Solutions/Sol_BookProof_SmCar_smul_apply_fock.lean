-- Prove2me | solution 1 for BookProof.SmCar.smul_apply_fock
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:56.138124+00:00
-- url     : https://prove2.me/submissions/e8b69746-0274-4d05-905a-80edc035c244

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.smul_apply_fock
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (x : FermiFock n) (S : Finset (Fin n)) :
    (c • x) S = c * x S := rfl
