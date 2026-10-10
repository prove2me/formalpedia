-- Prove2me | solution 1 for BookProof.HermiteExpWall.l2_psi_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:04:18.103873+00:00
-- url     : https://prove2.me/submissions/b8b44406-ae52-4073-a703-aade1754fed4

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.l2_psi_sq
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_even_pos
import Theorems.Thm_BookProof_HermiteExpWall_integral_psi_sq
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) : l2 (psi N) ^ 2 = gaussMoment (2 * N) := by

  rw [l2, Real.sq_sqrt]
  · exact integral_psi_sq N
  · rw [integral_psi_sq N]; exact (gaussMoment_even_pos N).le
