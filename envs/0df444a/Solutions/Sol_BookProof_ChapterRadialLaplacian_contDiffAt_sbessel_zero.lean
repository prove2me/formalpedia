-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:59:19.942519+00:00
-- url     : https://prove2.me/submissions/41099fc0-3ee4-4815-a4e3-494ebce8058f

-- Generated from ChapterRadialLaplacian.lean — theorem BookProof.ChapterRadialLaplacian.contDiffAt_sbessel_zero
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterSphericalBessel
import Definitions.Def_ChapterSphericalBesselODE
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian



open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open BookProof.ChapterRadialLaplacian

theorem solution{r : ℝ} (hr : r ≠ 0) : ContDiffAt ℝ 2 (sbessel 0) r := by
  have hs : sbessel 0 = fun r => Real.sin r / r := by
    funext r
    simp [sbessel, sbesselBase]
  rw [hs]
  exact (Real.contDiff_sin.contDiffAt).div contDiffAt_id hr
