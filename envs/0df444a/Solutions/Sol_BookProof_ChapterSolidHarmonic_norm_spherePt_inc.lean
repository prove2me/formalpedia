-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.norm_spherePt_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T14:30:39.372795+00:00
-- url     : https://prove2.me/submissions/911bcaa5-0ffa-44da-a636-3450e553d94f

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.norm_spherePt_inc
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
theorem solution {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r := by
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hue
  have hev : ⟪e, v⟫_ℝ = 0 := by rw [real_inner_comm]; exact hve
  have hnu : ∀ c : ℝ, ‖c • u‖ ^ 2 = c ^ 2 := by
    intro c; rw [norm_smul, hu, Real.norm_eq_abs]; simp [sq_abs]
  have hnv : ∀ c : ℝ, ‖c • v‖ ^ 2 = c ^ 2 := by
    intro c; rw [norm_smul, hv, Real.norm_eq_abs]; simp [sq_abs]
  have hne : ∀ c : ℝ, ‖c • e‖ ^ 2 = c ^ 2 := by
    intro c; rw [norm_smul, he, Real.norm_eq_abs]; simp [sq_abs]
  have hsq : ‖spherePt u v e r θ φ‖ ^ 2 = r ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [spherePt, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, huv, hue, hve, hvu, heu, hev, real_inner_self_eq_norm_sq,
      hnu, hnv, hne]
    have hs := Real.sin_sq_add_cos_sq φ
    have ht := Real.sin_sq_add_cos_sq θ
    linear_combination (r ^ 2 * Real.sin θ ^ 2) * hs + r ^ 2 * ht
  have h1 : 0 ≤ ‖spherePt u v e r θ φ‖ := norm_nonneg _
  nlinarith [hsq, h1, hr]
