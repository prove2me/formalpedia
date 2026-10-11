-- Prove2me | solution 1 for BookProof.SmDiracYukawa.fermiBilin_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:53.514392+00:00
-- url     : https://prove2.me/submissions/2d8ba479-5cb5-40c3-b7d0-684b2cac2366

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.fermiBilin_add
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (A B : Matrix (Fin n) (Fin n) ℂ) :
    fermiBilin (A + B) = fermiBilin A + fermiBilin B := by

  simp only [fermiBilin, Matrix.add_apply, add_smul]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
