-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:21.049528+00:00
-- url     : https://prove2.me/submissions/746d6386-969d-40e3-8695-d34c51ca885d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatPoly_eq_quadPolyMat
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_rotPoly
import Theorems.Thm_BookProof_ShiftedHermiteCore_coreEquivT_coe
import Theorems.Thm_BookProof_ShiftedHermiteCore_coreOpT_coe
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgLpT_smul
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
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
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    (α : Fin d →₀ ℕ) (h : hermiteTRLp O a k α ∈ polyGaussCoreT a k) :
    shiftedHMatOp a k (rotConj O c) b b' ⟨_, h⟩
      = (((quadSymbol c α + matShiftConst a k b b' : ℝ)) : ℂ) • hermiteTRLp O a k α := by

  have hcoe : (⟨hermiteTRLp O a k α, h⟩ : polyGaussCoreT a k)
      = coreEquivT a k (((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • rotPoly O (hermiteMv α)) := by
    apply Subtype.ext
    rw [coreEquivT_coe, pgLpT_smul]
    rfl
  rw [hcoe]
  simp only [shiftedHMatOp, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOpT_coe, map_smul, shiftedHMatPoly_eq_quadPolyMat a k hsym b b' ha hk,
    quadPolyMat_rotPoly hO, quadPoly_hermiteMv, map_smul, smul_add, smul_smul, smul_smul,
    ← add_smul, pgLpT_smul, hermiteTRLp, smul_smul]
  congr 1
  push_cast
  ring
