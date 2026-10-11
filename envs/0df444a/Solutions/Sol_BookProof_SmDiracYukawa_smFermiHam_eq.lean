-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiHam_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:54.515109+00:00
-- url     : https://prove2.me/submissions/537a74f8-b1af-42a7-b206-86d38fd220cb

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiHam_eq
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_fermiBilin_add
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    smFermiHam hD M z = smDirac hD + smYukawa M z := by

  rw [smFermiHam, smFermiMatrix, fermiBilin_add, smDirac, smYukawa]
