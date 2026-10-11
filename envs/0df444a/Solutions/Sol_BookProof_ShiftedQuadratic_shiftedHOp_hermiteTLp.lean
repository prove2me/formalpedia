-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:11.820693+00:00
-- url     : https://prove2.me/submissions/b244ecf9-4cda-49b6-a1c0-f0c8ffeb4d15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_eq_quadPoly
import Theorems.Thm_BookProof_ShiftedQuadratic_pgLpT_hermiteTLp
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
import Theorems.Thm_BookProof_ShiftedHermiteCore_coreEquivT_coe
import Theorems.Thm_BookProof_ShiftedHermiteCore_coreOpT_coe
import Theorems.Thm_BookProof_ShiftedHermiteCore_pgLpT_smul
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
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
theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) (α : Fin d →₀ ℕ)
    (h : hermiteTLp (shiftVec c b) (boostVec c b') α
      ∈ polyGaussCoreT (shiftVec c b) (boostVec c b')) :
    shiftedHOp (shiftVec c b) (boostVec c b') c b b' ⟨_, h⟩
      = (((quadSymbol c α + shiftConst c b b' : ℝ)) : ℂ)
          • hermiteTLp (shiftVec c b) (boostVec c b') α := by

  set a := shiftVec c b
  set k := boostVec c b'
  have hcoe : (⟨hermiteTLp a k α, h⟩ : polyGaussCoreT a k)
      = coreEquivT a k (((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • hermiteMv α) := by
    apply Subtype.ext
    rw [coreEquivT_coe, pgLpT_hermiteTLp]
  rw [hcoe]
  simp only [shiftedHOp, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOpT_coe, map_smul, shiftedHPoly_eq_quadPoly c b b' hc, quadPoly_hermiteMv,
    smul_add, smul_smul, smul_smul, ← add_smul, pgLpT_smul]
  rw [hermiteTLp, smul_smul]
  congr 1
  push_cast
  ring
