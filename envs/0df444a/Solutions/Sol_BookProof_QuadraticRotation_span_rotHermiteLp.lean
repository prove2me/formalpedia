-- Prove2me | solution 1 for BookProof.QuadraticRotation.span_rotHermiteLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:26:22.533626+00:00
-- url     : https://prove2.me/submissions/9076870d-648b-4075-8233-d807f18ecd63

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.span_rotHermiteLp
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_rotPoly_surjective
import Definitions.Def_ChapterHermiteProductCore
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
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Submodule.span ℂ (Set.range (rotHermiteLp (d := d) O)) = polyGaussCore (d := d) := by

  have hbase : Submodule.span ℂ
      (Set.range fun a : Fin d →₀ ℕ => pgLp (rotPoly O (hermiteMv a)))
      = polyGaussCore (d := d) := by
    have hrange : (Set.range fun a : Fin d →₀ ℕ => pgLp (rotPoly O (hermiteMv a)))
        = ((pgMap (d := d)).comp (rotPoly O).toLinearMap) ''
            (Set.range (hermiteMv (d := d))) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCore]
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact ⟨rotPoly O p, rfl⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := rotPoly_surjective hO p
      exact ⟨q, by simp [hq]⟩
  rw [← hbase]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    change pgLp (rotPoly O (hermiteMv a))
      ∈ Submodule.span ℂ (Set.range (rotHermiteLp (d := d) O))
    have h : pgLp (rotPoly O (hermiteMv a))
        = ((hermiteMvNorm a : ℝ) : ℂ) • rotHermiteLp O a := by
      rw [rotHermiteLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero a), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
