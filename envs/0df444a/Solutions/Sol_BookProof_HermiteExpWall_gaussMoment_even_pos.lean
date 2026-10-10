-- Prove2me | solution 1 for BookProof.HermiteExpWall.gaussMoment_even_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:01:24.931786+00:00
-- url     : https://prove2.me/submissions/ae0dd071-e440-42c1-87f6-ddfe9c94712f

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.gaussMoment_even_pos
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_step
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_zero
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
theorem solution (n : ℕ) : 0 < gaussMoment (2 * n) := by

  induction n with
  | zero =>
      rw [show 2 * 0 = 0 from rfl, gaussMoment_zero]
      exact Real.sqrt_pos.mpr (by positivity)
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, gaussMoment_step]
      positivity
