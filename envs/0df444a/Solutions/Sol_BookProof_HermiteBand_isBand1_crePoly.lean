-- Prove2me | solution 1 for BookProof.HermiteBand.isBand1_crePoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:33:41.865863+00:00
-- url     : https://prove2.me/submissions/5e1b3d60-56ff-4ee5-81ef-09129a285b9e

-- Generated from ChapterHermiteBandCalculus.lean — solution of BookProof.HermiteBand.isBand1_crePoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
import Theorems.Thm_BookProof_HermiteBand_band_crePoly
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
theorem solution (i : Fin d) : IsBand1 (crePoly i) := ⟨1, 1, zero_le_one, band_crePoly i⟩
