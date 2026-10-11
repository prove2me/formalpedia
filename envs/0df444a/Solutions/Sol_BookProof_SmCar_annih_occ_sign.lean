-- Prove2me | solution 1 for BookProof.SmCar.annih_occ_sign
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:12.762811+00:00
-- url     : https://prove2.me/submissions/bdf7e00d-1adc-4fda-9d4f-55cb848aca78

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.annih_occ_sign
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution : (annih (1 : Fin 2) (occ {0, 1})) {0} = -1 := by

  have h1 : ({1, 0} : Finset (Fin 2)) = {0, 1} := by decide
  have h2 : (({0} : Finset (Fin 2)).filter (fun j => j = (0 : Fin 2))).card = 1 := by decide
  simp [occ, annih, jwSign, EuclideanSpace.single_apply, h1, h2]
