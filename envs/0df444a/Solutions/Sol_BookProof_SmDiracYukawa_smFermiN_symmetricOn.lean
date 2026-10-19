-- Prove2me | solution 1 for BookProof.SmDiracYukawa.smFermiN_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:07:00.656177+00:00
-- url     : https://prove2.me/submissions/c4b2c157-cb9b-4f12-ab30-8b678ee587b7

-- Generated from ChapterSmDiracYukawa.lean — solution of BookProof.SmDiracYukawa.smFermiN_symmetricOn
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Theorems.Thm_BookProof_SmDiracYukawa_diagOp_symmetric
import Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_eq_diagOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterAbelianDiagonalCountable
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
theorem solution (om : Fin n → ℝ) (c0 : ℝ) :
    SymmetricOn (fullDom n) (onFull (smFermiN om c0)) := by

  intro x y
  rw [smFermiN_eq_diagOp]
  exact diagOp_symmetric (smFermiWeight om c0) (x : FermiFock n) (y : FermiFock n)
