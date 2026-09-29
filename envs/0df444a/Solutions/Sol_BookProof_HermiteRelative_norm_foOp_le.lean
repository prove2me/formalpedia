-- Prove2me | solution 1 for BookProof.HermiteRelative.norm_foOp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:35.927892+00:00
-- url     : https://prove2.me/submissions/09431047-992c-45bc-870e-017f833996e7

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.norm_foOp_le
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_norm_posL_le
import Theorems.Thm_BookProof_HermiteRelative_norm_momL_le
import Theorems.Thm_BookProof_HermiteRelative_foOp_apply
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
open BookProof.HermiteRelative










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (b b' : Fin d → ℝ) {e : ℝ} (he : 0 < e) (u : polyGaussCore (d := d)) :
    ‖foOp b b' u‖
      ≤ (∑ i, (|b i| + |b' i|)) * (e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖) := by

  classical
  set R : ℝ := e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ with hR
  have hR0 : 0 ≤ R := by
    have : 0 ≤ 2 / (c0 * e) := by positivity
    have h1 : 0 ≤ e * ‖quadOp c u‖ := by positivity
    have h2 : 0 ≤ (2 / (c0 * e)) * ‖(u : L2d d)‖ := by positivity
    linarith
  calc ‖foOp b b' u‖
      = ‖∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u)‖ := by
        rw [foOp_apply]
    _ ≤ ∑ i, ‖((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u‖ := norm_sum_le _ _
    _ ≤ ∑ i, (|b i| + |b' i|) * R := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hb : ‖((b i : ℝ) : ℂ) • posL i u‖ = |b i| * ‖posL i u‖ := by
          rw [norm_smul]
          simp
        have hb' : ‖((b' i : ℝ) : ℂ) • momL i u‖ = |b' i| * ‖momL i u‖ := by
          rw [norm_smul]
          simp
        have h1 : ‖posL i u‖ ≤ R := norm_posL_le c hc0 hc he i u
        have h2 : ‖momL i u‖ ≤ R := norm_momL_le c hc0 hc he i u
        calc ‖((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u‖
            ≤ ‖((b i : ℝ) : ℂ) • posL i u‖ + ‖((b' i : ℝ) : ℂ) • momL i u‖ := norm_add_le _ _
          _ = |b i| * ‖posL i u‖ + |b' i| * ‖momL i u‖ := by rw [hb, hb']
          _ ≤ |b i| * R + |b' i| * R := by
              have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (b i))
              have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (b' i))
              linarith
          _ = (|b i| + |b' i|) * R := by ring
    _ = (∑ i, (|b i| + |b' i|)) * R := by rw [Finset.sum_mul]
