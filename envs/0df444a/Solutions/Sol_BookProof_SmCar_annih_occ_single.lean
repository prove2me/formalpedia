-- Prove2me | solution 1 for BookProof.SmCar.annih_occ_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:11.370487+00:00
-- url     : https://prove2.me/submissions/aa8cf6e3-ae47-46a6-b7e6-abb3440049ea

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.annih_occ_single
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution : (annih (0 : Fin 2) (occ {0})) ∅ = 1 := by

  simp [occ, annih, jwSign, EuclideanSpace.single_apply]
