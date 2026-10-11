-- Prove2me | solution 1 for BookProof.SmCar.sum_apply_fock
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:54.764879+00:00
-- url     : https://prove2.me/submissions/584a12da-edbe-411c-b014-98968b4e5988

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.sum_apply_fock
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f : Fin n → FermiFock n) (S : Finset (Fin n)) :
    (∑ i : Fin n, f i) S = ∑ i : Fin n, (f i) S := by

  simp [WithLp.ofLp_sum]
