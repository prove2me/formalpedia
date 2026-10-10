-- Prove2me | solution 1 for BookProof.HermiteExpWall.bCoef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T06:21:07.353895+00:00
-- url     : https://prove2.me/submissions/651a2e54-a622-4915-b117-c5413c3a459c

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.bCoef_nonneg
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

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) : 0 ≤ bCoef m := by
    unfold bCoef; positivity

