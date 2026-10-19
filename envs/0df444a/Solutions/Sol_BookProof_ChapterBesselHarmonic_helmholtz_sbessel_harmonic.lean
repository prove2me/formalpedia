-- Prove2me | solution 1 for BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:27:36.855472+00:00
-- url     : https://prove2.me/submissions/2bd540e6-5c57-48de-89cf-017500822b91

-- Generated from ChapterBesselHarmonic.lean — solution of BookProof.ChapterBesselHarmonic.helmholtz_sbessel_harmonic
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Theorems.Thm_BookProof_ChapterBesselHarmonic_reduced_radial_sbessel
import Theorems.Thm_BookProof_ChapterLaplacianProduct_helmholtz_radial_mul_harmonic
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_contDiffAt_sbessel
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterBesselHarmonic




open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℝ E] (h3 : Module.finrank ℝ E = 3)
    {l : ℕ} {H : E → ℝ} {x : E} {p : ℝ} (hp : p ≠ 0) (hx : x ≠ 0)
    (hH : ContDiffAt ℝ 2 H x) (hharm : (Δ H) x = 0) (heuler : fderiv ℝ H x x = l * H x) :
    -(Δ fun y : E => (sbessel l (p * ‖y‖) / ‖y‖ ^ l) * H y) x
      = p ^ 2 * ((sbessel l (p * ‖x‖) / ‖x‖ ^ l) * H x) := by

  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr' : ‖x‖ ≠ 0 := ne_of_gt hr
  have hg : ContDiffAt ℝ 2 (fun s : ℝ => sbessel l (p * s) / s ^ l) ‖x‖ := by
    have hmul : ContDiffAt ℝ 2 (fun s : ℝ => p * s) ‖x‖ :=
      (contDiff_const.mul contDiff_id).contDiffAt
    have hb : ContDiffAt ℝ 2 (fun s : ℝ => sbessel l (p * s)) ‖x‖ :=
      (contDiffAt_sbessel l (mul_ne_zero hp hr')).comp ‖x‖ hmul
    have hpow : ContDiffAt ℝ 2 (fun s : ℝ => s ^ l) ‖x‖ := (contDiff_id.pow l).contDiffAt
    exact hb.div hpow (pow_ne_zero l hr')
  have hradial : deriv (deriv fun s : ℝ => sbessel l (p * s) / s ^ l) ‖x‖
      + (((Module.finrank ℝ E : ℝ) - 1 + 2 * l) / ‖x‖)
        * deriv (fun s : ℝ => sbessel l (p * s) / s ^ l) ‖x‖
      = -(p ^ 2) * (sbessel l (p * ‖x‖) / ‖x‖ ^ l) := by
    rw [h3]
    have hcoef : ((3 : ℕ) : ℝ) - 1 + 2 * (l : ℝ) = 2 + 2 * (l : ℝ) := by push_cast; ring
    rw [hcoef]
    exact reduced_radial_sbessel l hp hr'
  exact helmholtz_radial_mul_harmonic (g := fun s : ℝ => sbessel l (p * s) / s ^ l)
    (H := H) (l := l) (p := p) hx hg hH hharm heuler hradial
