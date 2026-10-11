-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:19.078472+00:00
-- url     : https://prove2.me/submissions/3d33f1c1-e982-4d88-913c-0a9daeeb4659

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.span_hermiteTRLp
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_surjective
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductBasis
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
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) :
    Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k)) = polyGaussCoreT a k := by

  have hbase : Submodule.span ℂ
      (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (rotPoly O (hermiteMv α)))
      = polyGaussCoreT a k := by
    have hrange : (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (rotPoly O (hermiteMv α)))
        = ((pgMapT a k).comp (rotPoly O).toLinearMap) '' (Set.range (hermiteMv (d := d))) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCoreT]
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact ⟨rotPoly O p, rfl⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := rotPoly_surjective hO p
      exact ⟨q, by simp [hq]⟩
  rw [← hbase]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    change pgLpT a k (rotPoly O (hermiteMv α))
      ∈ Submodule.span ℂ (Set.range (hermiteTRLp (d := d) O a k))
    have h : pgLpT a k (rotPoly O (hermiteMv α))
        = ((hermiteMvNorm α : ℝ) : ℂ) • hermiteTRLp O a k α := by
      rw [hermiteTRLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero α), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
