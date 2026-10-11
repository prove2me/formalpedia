-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.deriv_gIter_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:48.726444+00:00
-- url     : https://prove2.me/submissions/c1653a10-6b8c-4d07-932f-b9844ea14c60

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.deriv_gIter_eq
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_gIter_succ
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    deriv (gIter l) r = -r * gIter (l + 1) r := by

  rw [gIter_succ]; field_simp
