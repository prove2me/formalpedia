-- Prove2me | solution 1 for BookProof.HermiteBand.isBand2_weylProd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:35:21.406114+00:00
-- url     : https://prove2.me/submissions/696bcaa3-9f5c-485f-aec3-11823f096509

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.isBand2_weylProd
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_Band_add
import Theorems.Thm_BookProof_HermiteBand_Band_smul
import Theorems.Thm_BookProof_HermiteBand_Band_comp
import Theorems.Thm_BookProof_HermiteBand_IsBand1_add
import Theorems.Thm_BookProof_HermiteBand_IsBand2_add
import Theorems.Thm_BookProof_HermiteBand_IsBand1_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand2_smul
import Theorems.Thm_BookProof_HermiteBand_IsBand1_comp
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
theorem solution {S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hS : IsBand1 S) (hT : IsBand1 T) :
    IsBand2 (BookProof.YangMillsHermite.weylProd S T) := by

  rw [BookProof.YangMillsHermite.weylProd]
  exact IsBand2.smul _ ((hS.comp hT).add (hT.comp hS))
