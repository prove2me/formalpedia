-- Prove2me | solution 1 for BookProof.HermiteExpWall.aCoef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T06:21:06.191901+00:00
-- url     : https://prove2.me/submissions/e8a70960-9cf3-4b3c-9558-2106d7e390f3

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.aCoef_nonneg
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
theorem solution (m : ℕ) : 0 ≤ aCoef m := by
    unfold aCoef; positivity

