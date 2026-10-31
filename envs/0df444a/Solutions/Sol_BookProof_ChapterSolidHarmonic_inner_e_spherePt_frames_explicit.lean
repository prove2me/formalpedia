-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.inner_e_spherePt_frames_explicit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:23:49.494506+00:00
-- url     : https://prove2.me/submissions/f09b6322-3040-4147-9d11-77e65d2235b3

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


theorem solution (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (r θ φ : ℝ) : ⟪e, spherePt u v e r θ φ⟫_ℝ = r * Real.cos θ := by
  simp only [spherePt, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, he]
  rw [real_inner_comm u e, hue, real_inner_comm v e, hve]
  ring
