-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.sbessel_ode
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:39.073308+00:00
-- url     : https://prove2.me/submissions/f102f981-9efb-45b2-a97c-1125d94ed40a

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.sbessel_ode
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_eq
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_gIter_ode
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_pow_pred_coef
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbessel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * deriv (deriv (sbessel l)) r + 2 * r * deriv (sbessel l) r
      + (r ^ 2 - l * (l + 1)) * sbessel l r = 0 := by

  have hEq : deriv (sbessel l) =ᶠ[nhds r]
      fun x => x ^ l * ((l : ℝ) * gIter l x / x + deriv (gIter l) x) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx using (hasDerivAt_sbessel l hx).deriv
  have hquot : HasDerivAt (fun x : ℝ => (l : ℝ) * gIter l x / x)
      (((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2) r := by
    have h1 : HasDerivAt (fun x : ℝ => (l : ℝ) * gIter l x) ((l : ℝ) * deriv (gIter l) r) r :=
      ((diffAt_gIter l hr).hasDerivAt).const_mul _
    simpa using! h1.div (hasDerivAt_id r) hr
  have hinner : HasDerivAt (fun x : ℝ => (l : ℝ) * gIter l x / x + deriv (gIter l) x)
      ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
        + deriv (deriv (gIter l)) r) r :=
    hquot.add ((diffAt_deriv_gIter l hr).hasDerivAt)
  have hD : HasDerivAt (fun x : ℝ => x ^ l * ((l : ℝ) * gIter l x / x + deriv (gIter l) x))
      ((l : ℝ) * r ^ (l - 1) * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
        + r ^ l * ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
          + deriv (deriv (gIter l)) r)) r := (hasDerivAt_pow l r).mul hinner
  have h2nd : deriv (deriv (sbessel l)) r
      = r ^ l * ((l : ℝ) / r) * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
        + r ^ l * ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
          + deriv (deriv (gIter l)) r) := by
    rw [hEq.deriv_eq, hD.deriv, pow_pred_coef l hr]
  have hode := gIter_ode l hr
  rw [h2nd, (hasDerivAt_sbessel l hr).deriv, sbessel_eq]
  have expand : r ^ 2 * (r ^ l * ((l : ℝ) / r) * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
        + r ^ l * ((((l : ℝ) * deriv (gIter l) r * r - (l : ℝ) * gIter l r) / r ^ 2)
          + deriv (deriv (gIter l)) r))
      + 2 * r * (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r))
      + (r ^ 2 - l * (l + 1)) * (r ^ l * gIter l r)
      = r ^ l * r * (r * deriv (deriv (gIter l)) r + (2 * l + 2) * deriv (gIter l) r
          + r * gIter l r) := by
    field_simp
    ring
  rw [expand, hode, mul_zero]
