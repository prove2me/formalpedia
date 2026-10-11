-- Prove2me | solution 1 for BookProof.ChapterBesselHarmonic.reduced_radial_sbessel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:27:35.126592+00:00
-- url     : https://prove2.me/submissions/223a29d0-17d8-44b6-bf51-4b3c6c73b65b

-- Generated from ChapterBesselHarmonic.lean — solution of BookProof.ChapterBesselHarmonic.reduced_radial_sbessel
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Theorems.Thm_BookProof_ChapterBesselHarmonic_reduced_from_radial
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_sbessel
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbessel_scaled
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_radial_eigen
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterBesselHarmonic




open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    deriv (deriv fun s => sbessel l (p * s) / s ^ l) r
        + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => sbessel l (p * s) / s ^ l) r
      = -(p ^ 2) * (sbessel l (p * r) / r ^ l) := by

  have hpr : p * r ≠ 0 := mul_ne_zero hp hr
  have hR : DifferentiableAt ℝ (fun s => sbessel l (p * s)) r :=
    (hasDerivAt_sbessel_scaled l hp hr).differentiableAt
  have hRev : ∀ᶠ s in nhds r, DifferentiableAt ℝ (fun s => sbessel l (p * s)) s := by
    filter_upwards [isOpen_ne.mem_nhds hr] with s hs using
      (hasDerivAt_sbessel_scaled l hp hs).differentiableAt
  have hR' : DifferentiableAt ℝ (deriv fun s => sbessel l (p * s)) r := by
    have hEq : (deriv fun s => sbessel l (p * s)) =ᶠ[nhds r]
        fun s => deriv (sbessel l) (p * s) * p := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs using
        (hasDerivAt_sbessel_scaled l hp hs).deriv
    have hmul : DifferentiableAt ℝ (fun s : ℝ => p * s) r :=
      (differentiableAt_const p).mul differentiableAt_id
    have hcomp : DifferentiableAt ℝ (fun s : ℝ => deriv (sbessel l) (p * s)) r :=
      (diffAt_deriv_sbessel l hpr).comp r hmul
    exact (hcomp.mul_const p).congr_of_eventuallyEq hEq
  have hode : deriv (deriv fun s => sbessel l (p * s)) r
      + (2 / r) * deriv (fun s => sbessel l (p * s)) r
      + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r) = 0 := by
    have h := sbessel_radial_eigen l hp hr
    have hexp : (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r)
        = p ^ 2 * sbessel l (p * r) - ((l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r) := by
      ring
    rw [hexp]
    linarith [h]
  exact reduced_from_radial hr hR hR' hRev hode
