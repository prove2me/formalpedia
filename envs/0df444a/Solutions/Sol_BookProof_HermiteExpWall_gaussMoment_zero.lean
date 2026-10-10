-- Prove2me | solution 1 for BookProof.HermiteExpWall.gaussMoment_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:01:23.816589+00:00
-- url     : https://prove2.me/submissions/c9b1eb7a-e0a2-49d9-8bfc-595b8c9a7520

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gaussMoment_zero
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : gaussMoment 0 = Real.sqrt (2 * Real.pi) := by

  simpa [gaussMoment] using gint_one
