-- Prove2me | solution 1 for BookProof.HermiteExpWall.psi_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:42:01.467018+00:00
-- url     : https://prove2.me/submissions/413f5430-c3c7-49f7-b5f9-828ddad64afa

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.psi_apply
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (x : ℝ) : psi N x = x ^ N * gaussH x := by

  simp [psi, gaussPoly]
