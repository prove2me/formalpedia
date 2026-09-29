-- Prove2me | solution 1 for BookProof.HermiteRelative.le_relBound_of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T00:01:51.203697+00:00
-- url     : https://prove2.me/submissions/7b91e919-0a32-4a2c-b601-381d736be044

-- Generated from ChapterHermiteRelativeBound.lean — solution of BookProof.HermiteRelative.le_relBound_of_sq_le
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
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
theorem solution {t A B c0 e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc0 : 0 < c0) (he : 0 < e) (h : t ^ 2 ≤ (4 / c0) * (B * A)) :
    t ≤ e * A + (2 / (c0 * e)) * B := by

  have hrhs : 0 ≤ e * A + (2 / (c0 * e)) * B := by positivity
  have hsq : t ^ 2 ≤ (e * A + (2 / (c0 * e)) * B) ^ 2 := by
    have hcross : (4 / c0) * (B * A) ≤ 2 * (e * A) * ((2 / (c0 * e)) * B) := by
      have : 2 * (e * A) * ((2 / (c0 * e)) * B) = (4 / c0) * (B * A) := by
        field_simp
        ring
      rw [this]
    nlinarith [sq_nonneg (e * A), sq_nonneg ((2 / (c0 * e)) * B), h, hcross]
  nlinarith [hsq, hrhs]
