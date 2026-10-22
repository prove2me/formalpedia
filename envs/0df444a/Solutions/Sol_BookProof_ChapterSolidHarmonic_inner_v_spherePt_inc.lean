-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.inner_v_spherePt_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:30:36.275797+00:00
-- url     : https://prove2.me/submissions/ed43a97b-31d9-4233-953c-1b42d846fe63

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.inner_v_spherePt_inc
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic




open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

set_option maxHeartbeats 1000000 in

include he hu hue huv hv hve in
theorem solution (r θ φ : ℝ) :
    ⟪v, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.sin φ := by
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  simp only [spherePt, inner_add_right, real_inner_smul_right, hvu, hve,
    real_inner_self_eq_norm_sq, hv]
  ring
