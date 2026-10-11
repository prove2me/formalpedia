-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiHam_symmetricOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:07:01.682987+00:00
-- url     : https://prove2.me/submissions/342c1ca6-c8e8-4380-8b7e-f2ee986bb5da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_symmetric
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmDiracYukawa




open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {n : ℕ}
variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hh : hD.conjTranspose = hD) :
    SymmetricOn (fullDom n) (onFull (smFermiHam hD M z)) :=
  fun x y =>
    smFermiHam_symmetric z hh (x : FermiFock n) (y : FermiFock n)
