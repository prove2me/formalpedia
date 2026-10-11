-- Prove2me | solution 1 for BookProof.SmCar.fermiBilin_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:35:02.200711+00:00
-- url     : https://prove2.me/submissions/660908f6-259d-412f-87db-076f1308d6a3

-- Generated from ChapterSmCarAlgebra.lean — solution of BookProof.SmCar.fermiBilin_apply
import Mathlib
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.SmCar




open Finset

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : Matrix (Fin n) (Fin n) ℂ) (ψ : FermiFock n) :
    fermiBilin h ψ = ∑ i : Fin n, ∑ j : Fin n, h i j • creat i (annih j ψ) := by

  simp [fermiBilin, LinearMap.sum_apply]
