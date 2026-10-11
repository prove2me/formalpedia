-- Prove2me | solution 1 for BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:07.044106+00:00
-- url     : https://prove2.me/submissions/68a566d5-cd61-441f-af84-4a4b6124cc07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — solution of BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Theorems.Thm_BookProof_ShiftedHermiteCore_polyGaussCoreT_dense
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_hermiteTRLp_mem_coreT
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_hermiteTRLp
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_deficiencyTrivialAt
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_rotConj_symmetric
import Theorems.Thm_BookProof_StoneEigenflow_exists_diagonal_stone_flow
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
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

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (shiftedHMatOp a k (rotConj O c) b b') T.op ∧
      IsStoneFlow T U ∧
      ∀ (α : Fin d →₀ ℕ) (t : ℝ),
        U t (hermiteTRLp O a k α)
          = Complex.exp (-(Complex.I * ((quadSymbol c α + matShiftConst a k b b' : ℝ) : ℂ) * t))
              • hermiteTRLp O a k α :=
  exists_diagonal_stone_flow _ (polyGaussCoreT_dense a k)
      (shiftedHMatOp_rotConj_symmetric hO c a k b b' hsym ha hk)
      ⟨shiftedHMatOp_rotConj_deficiencyTrivialAt hO c a k b b' hsym ha hk (by simp),
        shiftedHMatOp_rotConj_deficiencyTrivialAt hO c a k b b' hsym ha hk (by simp)⟩
      (fun α => (⟨hermiteTRLp O a k α, hermiteTRLp_mem_coreT O a k α⟩ : polyGaussCoreT a k))
      (fun α => quadSymbol c α + matShiftConst a k b b')
      (fun α => shiftedHMatOp_hermiteTRLp hO c a k b b' hsym ha hk α
        (hermiteTRLp_mem_coreT O a k α))
