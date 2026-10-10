-- Prove2me | solution 1 for BookProof.HermiteBandHigher.isBandR1_crePoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:52:56.559765+00:00
-- url     : https://prove2.me/submissions/f93fa81c-00dd-4f8b-b88e-95acf3d4a7fd

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.isBandR1_crePoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_isBand1_isBandR_one
import Theorems.Thm_BookProof_HermiteBand_isBand1_crePoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteProductBasis

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) : IsBandR 1 1 (crePoly i) := isBand1_isBandR_one (isBand1_crePoly i)
