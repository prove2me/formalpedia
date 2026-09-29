-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.span_hermiteTLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:11.012805+00:00
-- url     : https://prove2.me/submissions/f82556f1-8d12-44d0-8008-dcbf0ca13d19

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.span_hermiteTLp
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) :
    Submodule.span ℂ (Set.range (hermiteTLp (d := d) a k)) = polyGaussCoreT a k := by

  have hbase : Submodule.span ℂ
      (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (hermiteMv α)) = polyGaussCoreT a k := by
    have hrange : (Set.range fun α : Fin d →₀ ℕ => pgLpT a k (hermiteMv α))
        = (pgMapT a k) '' (Set.range (hermiteMv (d := d))) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, span_hermiteMv, Submodule.map_top, polyGaussCoreT]
  rw [← hbase]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    change pgLpT a k (hermiteMv α) ∈ Submodule.span ℂ (Set.range (hermiteTLp (d := d) a k))
    have h : pgLpT a k (hermiteMv α) = ((hermiteMvNorm α : ℝ) : ℂ) • hermiteTLp a k α := by
      rw [hermiteTLp, smul_smul, mul_inv_cancel₀ (hermiteMvNorm_ne_zero α), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
