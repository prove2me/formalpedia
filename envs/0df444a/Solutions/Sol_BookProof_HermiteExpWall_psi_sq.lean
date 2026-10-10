-- Prove2me | solution 1 for BookProof.HermiteExpWall.psi_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:03:50.82575+00:00
-- url     : https://prove2.me/submissions/48b27940-8d4c-4720-bb55-1d17b733c856

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.psi_sq
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_psi_apply
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGhostField
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.HermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (x : ℝ) : psi N x ^ 2 = x ^ (2 * N) * gaussW x := by

  rw [psi_apply, mul_pow, ← gaussH_sq, pow_mul]
  ring_nf
