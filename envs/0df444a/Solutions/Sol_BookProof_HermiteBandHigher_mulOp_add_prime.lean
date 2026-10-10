-- Prove2me | solution 1 for BookProof.HermiteBandHigher.mulOp_add_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:09:18.221827+00:00
-- url     : https://prove2.me/submissions/c15e48ba-9300-4343-af72-7e5fe67c9e49

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.YangMillsHermite.mulOp_add'
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteBandCalculus
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterF7
open BookProof.HermiteBandHigher




noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (f g : MvPolynomial (Fin d) ℂ) : BookProof.YangMillsHermite.mulOp (f + g) = BookProof.YangMillsHermite.mulOp f + BookProof.YangMillsHermite.mulOp g := by

  refine LinearMap.ext fun p => ?_
  simp [BookProof.YangMillsHermite.mulOp, add_mul]
