-- Prove2me | solution 1 for BookProof.HermiteRelative.norm_posL_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:09.850101+00:00
-- url     : https://prove2.me/submissions/91fed3b1-5ab2-4dc9-8d6e-8d359595643d

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.norm_posL_le
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Theorems.Thm_BookProof_HermiteRelative_norm_posL_sq_le
import Theorems.Thm_BookProof_HermiteRelative_le_relBound_of_sq_le
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
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ :=
  le_relBound_of_sq_le (norm_nonneg _) (norm_nonneg _) hc0 he
      (norm_posL_sq_le c hc0 hc i u)
