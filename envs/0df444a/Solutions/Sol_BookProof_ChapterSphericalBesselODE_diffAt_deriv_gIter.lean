-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:40.651787+00:00
-- url     : https://prove2.me/submissions/3ef1a4d3-e995-4771-b900-358c85757f08

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_contDiffOn_gIter
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    DifferentiableAt ℝ (deriv (gIter l)) r :=
  (((contDiffOn_gIter l).deriv_of_isOpen (m := (⊤ : ℕ∞)) isOpen_ne (by simp)).differentiableOn
      (by simp)).differentiableAt (isOpen_ne.mem_nhds hr)
