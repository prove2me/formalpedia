-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiHam_norm_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:06:56.424988+00:00
-- url     : https://prove2.me/submissions/3de47cb1-2561-4621-a9a4-8be989f4bf7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiHam_norm_le
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmCar_norm_fermiBilin_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ψ : FermiFock n) :
    ‖smFermiHam hD M z ψ‖
      ≤ (∑ i : Fin n, ∑ j : Fin n, ‖smFermiMatrix hD M z i j‖) * ‖ψ‖ := norm_fermiBilin_le _ ψ
