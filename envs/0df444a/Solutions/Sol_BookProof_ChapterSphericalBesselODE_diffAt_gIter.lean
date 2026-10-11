-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.diffAt_gIter
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:39.28853+00:00
-- url     : https://prove2.me/submissions/9997c172-681d-468c-bd57-87fe82eb0c9e

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.diffAt_gIter
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_contDiffOn_gIter
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) : DifferentiableAt ℝ (gIter l) r := ((contDiffOn_gIter l).differentiableOn (by simp)).differentiableAt (isOpen_ne.mem_nhds hr)
