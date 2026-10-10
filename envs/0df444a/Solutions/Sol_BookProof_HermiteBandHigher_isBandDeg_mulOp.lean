-- Prove2me | solution 1 for BookProof.HermiteBandHigher.isBandDeg_mulOp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:59:18.821727+00:00
-- url     : https://prove2.me/submissions/a749940e-0ae8-4b41-9cf6-ecd443e9668d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterHermiteBandCalculusHigher.lean — solution of BookProof.HermiteBandHigher.isBandDeg_mulOp
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculusHigher
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_le
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_le
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandR_sum
import Theorems.Thm_BookProof_HermiteBandHigher_IsBandDeg_sum
import Theorems.Thm_BookProof_HermiteBandHigher_mulOp_sum
import Theorems.Thm_BookProof_HermiteBandHigher_isBandDeg_mulOp_monomial
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
open BookProof.ChapterF7

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : MvPolynomial (Fin d) ℂ) :
    IsBandDeg p.totalDegree (mulOp p) := by

  classical
  have hp : p = ∑ s ∈ p.support, (monomial s (coeff s p) : MvPolynomial (Fin d) ℂ) :=
    (MvPolynomial.support_sum_monomial_coeff p).symm
  rw [show mulOp p = ∑ s ∈ p.support, mulOp (monomial s (coeff s p)) by
    conv_lhs => rw [hp]
    rw [mulOp_sum]]
  refine IsBandDeg.sum _ _ fun s hs => ?_
  refine IsBandDeg.le ?_ (isBandDeg_mulOp_monomial s (coeff s p))
  exact MvPolynomial.le_totalDegree hs
