-- Prove2me | solution 1 for BookProof.HermiteExpWall.gaussMoment_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:59:42.140278+00:00
-- url     : https://prove2.me/submissions/b76f55e9-642d-4c0b-8175-1440c7a0f097

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gaussMoment_eq_integral
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.HermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    gaussMoment k = ∫ x : ℝ, x ^ k * gaussW x := by

  simp [gaussMoment, gint]
