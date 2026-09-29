-- Prove2me | solution 1 for BookProof.HermiteBand.isBand1_foPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:56.18989+00:00
-- url     : https://prove2.me/submissions/373b6eab-a988-4fbd-b6d5-f6847ac51f6c

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.isBand1_foPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_Band_add
import Theorems.Thm_BookProof_HermiteBand_Band_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand1_add
import Theorems.Thm_BookProof_HermiteBand_IsBand2_add
import Theorems.Thm_BookProof_HermiteBand_IsBand1_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand2_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand1_sum
import Theorems.Thm_BookProof_HermiteBand_IsBand2_sum
import Theorems.Thm_BookProof_HermiteBand_isBand1_mulXPoly
import Theorems.Thm_BookProof_HermiteBand_isBand1_momPoly
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
theorem solution (b b' : Fin d → ℝ) : IsBand1 (BookProof.HermiteRelative.foPoly b b') := by

  rw [BookProof.HermiteRelative.foPoly]
  exact IsBand1.sum _ _ fun i _ =>
    ((isBand1_mulXPoly i).smul _).add ((isBand1_momPoly i).smul _)
