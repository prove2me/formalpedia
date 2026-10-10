-- Prove2me | solution 1 for BookProof.HermiteBandHigher.isBand1_iff_isBandDeg_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:52:21.979265+00:00
-- url     : https://prove2.me/submissions/bcf4b5d2-41c8-4b74-bdfd-d5203da6c3e1

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.isBand1_iff_isBandDeg_one
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_isBandDeg
import Theorems.Thm_BookProof_HermiteBandHigher_isBand1_isBandR_one
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteBand

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ} :
    IsBand1 T → IsBandDeg 1 T := fun h => (isBand1_isBandR_one h).isBandDeg
