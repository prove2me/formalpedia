-- Prove2me | solution 1 for BookProof.HermiteExpWall.integral_psi_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:03:51.901889+00:00
-- url     : https://prove2.me/submissions/8970b4a2-7e19-437b-86ff-bc81e6d17c6b

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.integral_psi_sq
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_eq_integral
import Theorems.Thm_BookProof_HermiteExpWall_psi_sq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.HermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) : ∫ x : ℝ, psi N x ^ 2 = gaussMoment (2 * N) := by

  rw [gaussMoment_eq_integral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => psi_sq N x)
