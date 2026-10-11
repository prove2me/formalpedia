-- Prove2me | solution 1 for BookProof.HermiteExpWall.gint_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:39.145291+00:00
-- url     : https://prove2.me/submissions/45294ea6-2a87-491c-ba76-751626475f63

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gint_X_pow
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


theorem solution (k : ℕ) : gint ((Polynomial.X : Polynomial ℝ) ^ k) = gaussMoment k := by rfl
