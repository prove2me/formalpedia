-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_rotHermiteLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:58:55.237979+00:00
-- url     : https://prove2.me/submissions/102bdc97-b3e7-44b7-ac73-768c85866c86

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.quadOpMat_rotHermiteLp
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_rotPoly
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreEquiv_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coe
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_pgLp_smul
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a : Fin d →₀ ℕ) (h : rotHermiteLp O a ∈ polyGaussCore (d := d)) :
    quadOpMat (rotConj O c) ⟨rotHermiteLp O a, h⟩
      = ((quadSymbol c a : ℝ) : ℂ) • rotHermiteLp O a := by

  have hcoe : (⟨rotHermiteLp O a, h⟩ : polyGaussCore (d := d))
      = coreEquiv (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • rotPoly O (hermiteMv a)) := by
    apply Subtype.ext
    rw [coreEquiv_coe, pgLp_smul]
    rfl
  rw [hcoe]
  simp only [quadOpMat, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOp_coe, map_smul, quadPolyMat_rotPoly hO, quadPoly_hermiteMv, map_smul,
    smul_comm, pgLp_smul, pgLp_smul]
  rfl
