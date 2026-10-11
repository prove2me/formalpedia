-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.sbessel_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:41.762965+00:00
-- url     : https://prove2.me/submissions/b5a91b51-6cb5-4b1f-8047-48ccddd95f40

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.sbessel_recurrence
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_eq
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_deriv_gIter_eq
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_gIter_pred_eq
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    sbessel l r + sbessel (l + 2) r = ((2 * (l + 1) + 1) / r) * sbessel (l + 1) r := by

  have hg : gIter l r = (2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r :=
    gIter_pred_eq l hr
  have hstep : deriv (gIter (l + 1)) r = -r * gIter (l + 2) r := deriv_gIter_eq (l + 1) hr
  rw [sbessel_eq, sbessel_eq, sbessel_eq, hg, hstep]
  field_simp
  ring
