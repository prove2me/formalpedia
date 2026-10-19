-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:12.879974+00:00
-- url     : https://prove2.me/submissions/dc11941c-9643-45fe-a0da-a4e25c0e334e

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHOp_symmetric
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_hermiteTLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_symmetricOn_of_diagonal
import Theorems.Thm_BookProof_ShiftedHermiteCore_orthonormal_hermiteTLp
import Theorems.Thm_BookProof_ShiftedHermiteCore_span_hermiteTLp
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    SymmetricOn (polyGaussCoreT (shiftVec c b) (boostVec c b'))
      (shiftedHOp (shiftVec c b) (boostVec c b') c b b') :=
  symmetricOn_of_diagonal (hermiteTLp (shiftVec c b) (boostVec c b'))
      (orthonormal_hermiteTLp _ _) (fun α => quadSymbol c α + shiftConst c b b')
      (span_hermiteTLp _ _) _ (fun α h => shiftedHOp_hermiteTLp c b b' hc α h)
