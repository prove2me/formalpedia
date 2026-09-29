-- Prove2me | solution 1 for BookProof.HermiteBand.isBand1_momPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:57.124566+00:00
-- url     : https://prove2.me/submissions/6141042a-7c7e-423b-83a8-e118e3fa9e54

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.isBand1_momPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_Band_add
import Theorems.Thm_BookProof_HermiteBand_Band_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand1_add
import Theorems.Thm_BookProof_HermiteBand_IsBand2_add
import Theorems.Thm_BookProof_HermiteBand_IsBand1_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand2_smul
import Theorems.Thm_BookProof_HermiteBand_isBand1_crePoly
import Theorems.Thm_BookProof_HermiteBand_isBand1_annPoly
import Theorems.Thm_BookProof_HermiteBand_momPoly_eq
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBand








noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) : IsBand1 (momPoly i) := by

  rw [momPoly_eq]
  exact ((isBand1_crePoly i).smul _).add ((isBand1_annPoly i).smul _)
