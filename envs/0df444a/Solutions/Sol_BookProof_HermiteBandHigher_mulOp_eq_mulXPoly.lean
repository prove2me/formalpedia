-- Prove2me | solution 1 for BookProof.HermiteBandHigher.mulOp_eq_mulXPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:07:46.845441+00:00
-- url     : https://prove2.me/submissions/3c4a03fc-f1e5-4009-9a74-b16d4369f434

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.YangMillsHermite.mulOp_eq_mulXPoly
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) :
    BookProof.YangMillsHermite.mulOp (X i : MvPolynomial (Fin d) ℂ) = mulXPoly i := by

  refine LinearMap.ext fun p => ?_
  simp [BookProof.YangMillsHermite.mulOp, mulXPoly]
