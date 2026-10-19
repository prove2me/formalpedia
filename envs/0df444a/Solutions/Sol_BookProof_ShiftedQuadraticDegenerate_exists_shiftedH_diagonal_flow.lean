-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:03.90413+00:00
-- url     : https://prove2.me/submissions/3de389cd-c8c3-4250-921d-ad98e5bfccd2

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_ShiftedHermiteCore_hermiteTLp_mem_coreT
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedCore_dense
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_hermiteTLp
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_symmetric
import Theorems.Thm_BookProof_StoneEigenflow_exists_diagonal_stone_flow
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.ShiftedQuadraticDegenerate




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.StoneBridge

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension
        (shiftedHOp (shiftVec c b) (boostVec c b') c b b') T.op ∧
      IsStoneFlow T U ∧
      ∀ (α : Fin d →₀ ℕ) (t : ℝ),
        U t (hermiteTLp (shiftVec c b) (boostVec c b') α)
          = Complex.exp (-(Complex.I * ((quadSymbol c α + shiftConst c b b' : ℝ) : ℂ) * t))
              • hermiteTLp (shiftVec c b) (boostVec c b') α :=
  exists_diagonal_stone_flow _ (shiftedCore_dense c b b')
    (shiftedHOp_symmetric c b b' hc) (shiftedHOp_essentiallySelfAdjoint c b b' hc)
    (fun α => (⟨hermiteTLp (shiftVec c b) (boostVec c b') α,
      hermiteTLp_mem_coreT _ _ α⟩ : polyGaussCoreT (shiftVec c b) (boostVec c b')))
    (fun α => quadSymbol c α + shiftConst c b b')
    (fun α => shiftedHOp_hermiteTLp c b b' hc α (hermiteTLp_mem_coreT _ _ α))

end
