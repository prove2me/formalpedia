-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.norm_spherePt_frames_explicit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:41:56.118985+00:00
-- url     : https://prove2.me/submissions/362face2-743c-4231-aef1-e40a7c6a54eb

-- Corrected statement of BookProof.ChapterSolidHarmonic.inner_u_spherePt.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterSolidHarmonic.lean (Lean 4.28) and timepiece331/BookProof/ChapterSolidHarmonic.lean (Lean 4.33.1).
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)


theorem solution (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r := by
  have hsq : ‖spherePt u v e r θ φ‖ ^ 2 = r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [spherePt, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hu, hv, he]
    rw [real_inner_comm u v, huv, real_inner_comm u e, hue, real_inner_comm v e, hve]
    have hpoly :
        r ^ 2 * (Real.sin θ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2) + Real.cos θ ^ 2) = r ^ 2 := by
      rw [Real.cos_sq_add_sin_sq φ, mul_one, Real.sin_sq_add_cos_sq θ]
      ring
    simp [starRingEnd_apply]
    convert hpoly using 1
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) hr).mp hsq

