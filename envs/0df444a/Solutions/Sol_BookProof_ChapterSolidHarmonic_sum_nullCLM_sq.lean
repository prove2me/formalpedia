-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.sum_nullCLM_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:24:58.742799+00:00
-- url     : https://prove2.me/submissions/45d02c73-97c8-4fd0-8d90-28886fc9b289

import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterRadialLaplacian
-- Generated from ChapterSolidHarmonic.lean — theorem BookProof.ChapterSolidHarmonic.sum_nullCLM_sq
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
theorem h43_sumsq_aux (u v : E) :
    ∑ i, (⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ) * ⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner u v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm v]

theorem solution {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) :
    ∑ i, (nullCLM u v (stdOrthonormalBasis ℝ E i)) ^ 2 = 0 := by
  have h1 := h43_sumsq_aux u u
  have h2 := h43_sumsq_aux v v
  have h3 := h43_sumsq_aux u v
  rw [real_inner_self_eq_norm_sq, hu] at h1
  rw [real_inner_self_eq_norm_sq, hv] at h2
  rw [huv] at h3
  simp only [nullCLM_apply]
  have : ∀ i, ((⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ : ℂ) + Complex.I * (⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ : ℂ)) ^ 2
      = ((⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ * ⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ : ℝ) : ℂ)
        - ((⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ * ⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ : ℝ) : ℂ)
        + 2 * Complex.I * ((⟪u, (stdOrthonormalBasis ℝ E) i⟫_ℝ * ⟪v, (stdOrthonormalBasis ℝ E) i⟫_ℝ : ℝ) : ℂ) := by
    intro i; push_cast; ring_nf; rw [Complex.I_sq]; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum, h1, h2, h3]
  simp

