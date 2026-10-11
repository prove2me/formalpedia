-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:46.85233+00:00
-- url     : https://prove2.me/submissions/e5ed4760-ec16-4298-b2cc-4b5e44411a69

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_ode
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbessel_scaled
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_sbessel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    -(deriv (deriv (fun s => sbessel l (p * s))) r
        + (2 / r) * deriv (fun s => sbessel l (p * s)) r
        - ((l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r))
      = p ^ 2 * sbessel l (p * r) := by

  have hpr : p * r ≠ 0 := mul_ne_zero hp hr
  have hEq : deriv (fun s => sbessel l (p * s)) =ᶠ[nhds r]
      fun x => deriv (sbessel l) (p * x) * p := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using
      (hasDerivAt_sbessel_scaled l hp hx).deriv
  have hderiv2 : DifferentiableAt ℝ (deriv (sbessel l)) (p * r) := diffAt_deriv_sbessel l hpr
  have hc : HasDerivAt (fun s : ℝ => p * s) p r := by
    simpa using (hasDerivAt_id r).const_mul p
  have hD2 : HasDerivAt (fun x : ℝ => deriv (sbessel l) (p * x) * p)
      (deriv (deriv (sbessel l)) (p * r) * p * p) r :=
    (hderiv2.hasDerivAt.comp r hc).mul_const p
  have hsecond : deriv (deriv (fun s => sbessel l (p * s))) r
      = deriv (deriv (sbessel l)) (p * r) * p * p := by
    rw [hEq.deriv_eq, hD2.deriv]
  have hode := sbessel_ode l hpr
  rw [hsecond, (hasDerivAt_sbessel_scaled l hp hr).deriv]
  field_simp
  nlinarith [hode]
