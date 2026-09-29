-- Prove2me | solution 1 for BookProof.HermiteBand.isBand1_annPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:32:48.641951+00:00
-- url     : https://prove2.me/submissions/7056bd4d-0659-4459-8310-f03a75ef0e58

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.isBand1_annPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_band_annPoly
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
theorem solution (i : Fin d) : IsBand1 (annPoly i) := ⟨1, 1, zero_le_one, band_annPoly i⟩
