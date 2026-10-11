-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:37.805733+00:00
-- url     : https://prove2.me/submissions/2eb7f23a-936d-46cc-b4d7-769eb398d26e

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_pow_pred_coef
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (sbessel l) (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)) r := by

  have hD : HasDerivAt (fun x : ℝ => x ^ l * gIter l x)
      ((l : ℝ) * r ^ (l - 1) * gIter l r + r ^ l * deriv (gIter l) r) r :=
    (hasDerivAt_pow l r).mul ((diffAt_gIter l hr).hasDerivAt)
  have hfun : (fun x : ℝ => x ^ l * gIter l x) = sbessel l := rfl
  rw [hfun] at hD
  have hval : r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)
      = (l : ℝ) * r ^ (l - 1) * gIter l r + r ^ l * deriv (gIter l) r := by
    rw [pow_pred_coef l hr]
    field_simp
  rw [hval]
  exact hD
