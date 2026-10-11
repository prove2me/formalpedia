-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_symmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:35.884857+00:00
-- url     : https://prove2.me/submissions/2d5e407c-9bf8-4345-a9ac-d07c6f0bbaa4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_rotConj_symmetric
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_orthonormal_hermiteTRLp
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_span_hermiteTRLp
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_hermiteTRLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_symmetricOn_of_diagonal
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) :
    SymmetricOn (polyGaussCoreT a k) (shiftedHMatOp a k (rotConj O c) b b') :=
  symmetricOn_of_diagonal (hermiteTRLp O a k) (orthonormal_hermiteTRLp hO a k)
      (fun α => quadSymbol c α + matShiftConst a k b b') (span_hermiteTRLp hO a k) _
      (fun α h => shiftedHMatOp_hermiteTRLp hO c a k b b' hsym ha hk α h)
