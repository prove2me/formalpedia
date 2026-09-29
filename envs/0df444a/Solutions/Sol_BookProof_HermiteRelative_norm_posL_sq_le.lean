-- Prove2me | solution 1 for BookProof.HermiteRelative.norm_posL_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:00.823582+00:00
-- url     : https://prove2.me/submissions/0e726f7d-5a29-43be-a96d-a1e8ddcda0d3

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.norm_posL_sq_le
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_re_inner_oscL_eq
import Theorems.Thm_BookProof_HermiteRelative_re_inner_oscL_le_quadOp
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
    (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ^ 2 ≤ (4 / c0) * (‖(u : L2d d)‖ * ‖quadOp c u‖) := by

  have h1 : ‖posL i u‖ ^ 2 / 4 ≤ (inner ℂ (u : L2d d) (oscL i u) : ℂ).re := by
    rw [re_inner_oscL_eq]
    nlinarith [sq_nonneg ‖momL i u‖]
  have h2 := re_inner_oscL_le_quadOp c hc0 hc i u
  have h3 : (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ :=
    re_inner_le_norm (𝕜 := ℂ) (u : L2d d) (quadOp c u)
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, h2, h3]
