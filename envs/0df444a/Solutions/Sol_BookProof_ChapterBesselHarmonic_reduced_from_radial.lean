-- Prove2me | solution 1 for BookProof.ChapterBesselHarmonic.reduced_from_radial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:28:05.100302+00:00
-- url     : https://prove2.me/submissions/d972ce4d-bc89-42f4-9b56-a02efddda4f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterBesselHarmonic.lean — solution of BookProof.ChapterBesselHarmonic.reduced_from_radial
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Theorems.Thm_BookProof_ChapterBesselHarmonic_hasDerivAt_quot
open BookProof.ChapterBesselHarmonic




open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

set_option maxHeartbeats 1000000 in
theorem solution {R : ℝ → ℝ} {l : ℕ} {p r : ℝ} (hr : r ≠ 0)
    (hR : DifferentiableAt ℝ R r) (hR' : DifferentiableAt ℝ (deriv R) r)
    (hRev : ∀ᶠ s in nhds r, DifferentiableAt ℝ R s)
    (hode : deriv (deriv R) r + (2 / r) * deriv R r
      + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * R r = 0) :
    deriv (deriv fun s => R s / s ^ l) r
        + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => R s / s ^ l) r
      = -(p ^ 2) * (R r / r ^ l) := by

  have hne : ∀ᶠ s in nhds r, s ≠ 0 := isOpen_ne.mem_nhds hr
  have hEq : (deriv fun s => R s / s ^ l) =ᶠ[nhds r]
      fun s => deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1) := by
    filter_upwards [hRev, hne] with s hs hs0 using (hasDerivAt_quot hs0 hs).deriv
  have h1 : HasDerivAt (fun s => deriv R s / s ^ l)
      (deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1)) r :=
    hasDerivAt_quot hr hR'
  have hq : HasDerivAt (fun s => R s / s ^ (l + 1))
      (deriv R r / r ^ (l + 1) - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1)) r := by
    have h := hasDerivAt_quot (l := l + 1) hr hR
    push_cast at h
    exact h
  have h2 : HasDerivAt (fun s => (l : ℝ) * R s / s ^ (l + 1))
      ((l : ℝ) * (deriv R r / r ^ (l + 1) - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1))) r := by
    have h := hq.const_mul (l : ℝ)
    have hfun : (fun s => (l : ℝ) * (R s / s ^ (l + 1)))
        = fun s => (l : ℝ) * R s / s ^ (l + 1) := by
      funext s; ring
    rw [hfun] at h
    exact h
  have h12 : HasDerivAt (fun s => deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1))
      ((deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1))
        - (l : ℝ) * (deriv R r / r ^ (l + 1)
            - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1))) r := h1.sub h2
  have hderiv2 : deriv (deriv fun s => R s / s ^ l) r
      = (deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1))
        - (l : ℝ) * (deriv R r / r ^ (l + 1)
            - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1)) := by
    rw [hEq.deriv_eq, h12.deriv]
  have hderiv1 : deriv (fun s => R s / s ^ l) r
      = deriv R r / r ^ l - (l : ℝ) * R r / r ^ (l + 1) := (hasDerivAt_quot hr hR).deriv
  rw [hderiv2, hderiv1]
  have expand : ((deriv (deriv R) r / r ^ l - (l : ℝ) * deriv R r / r ^ (l + 1))
        - (l : ℝ) * (deriv R r / r ^ (l + 1)
            - ((l : ℝ) + 1) * R r / r ^ (l + 1 + 1)))
      + ((2 + 2 * (l : ℝ)) / r) * (deriv R r / r ^ l - (l : ℝ) * R r / r ^ (l + 1))
      = (1 / r ^ l) * (deriv (deriv R) r + (2 / r) * deriv R r
          + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * R r) - p ^ 2 * (R r / r ^ l) := by
    field_simp
    ring
  rw [expand, hode]
  ring
