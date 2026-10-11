-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:50.392242+00:00
-- url     : https://prove2.me/submissions/5dbd7ef6-23ea-49c9-b788-08b65230a820
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_stone_flow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_symmetric
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatCore_dense
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
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
theorem solution {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension
        (shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b') T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ (shiftedHMatCore_dense b b')
      (shiftedHMatOp_symmetric hA hdet b b')
      (shiftedHMatOp_essentiallySelfAdjoint hA hdet b b')
