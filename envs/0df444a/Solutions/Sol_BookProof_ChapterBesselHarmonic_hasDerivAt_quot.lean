-- Prove2me | solution 1 for BookProof.ChapterBesselHarmonic.hasDerivAt_quot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:27:33.721134+00:00
-- url     : https://prove2.me/submissions/2570cbcc-bd04-4e63-8b20-064ed2c84c85

-- Generated from ChapterBesselHarmonic.lean — solution of BookProof.ChapterBesselHarmonic.hasDerivAt_quot
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_pow_pred_coef
import Definitions.Def_ChapterSphericalBessel
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterBesselHarmonic




open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution {R : ℝ → ℝ} {l : ℕ} {s : ℝ} (hs : s ≠ 0) (hR : DifferentiableAt ℝ R s) :
    HasDerivAt (fun t => R t / t ^ l)
      (deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1)) s := by

  have hp : HasDerivAt (fun t : ℝ => t ^ l) ((l : ℝ) * s ^ (l - 1)) s := hasDerivAt_pow l s
  have h := (hR.hasDerivAt).div hp (pow_ne_zero l hs)
  convert h using 1 <;> (first | rfl | (rw [pow_pred_coef l hs]; field_simp; ring))
