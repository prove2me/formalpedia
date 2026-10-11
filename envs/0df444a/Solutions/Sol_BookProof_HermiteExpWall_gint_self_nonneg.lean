-- Prove2me | solution 1 for BookProof.HermiteExpWall.gint_self_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:56:35.2925+00:00
-- url     : https://prove2.me/submissions/7887a4a5-f111-4152-b626-12a18ffd9f9f

-- Generated from ChapterHermiteExpWall.lean — theorem BookProof.HermiteExpWall.gint_self_nonneg
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteCore
open BookProof.QgHermiteCore
open BookProof.HermiteExpWall



open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore

noncomputable section
open BookProof.HermiteExpWall

theorem solution(q : Polynomial ℝ) : 0 ≤ gint (q * q) := by
  unfold gint
  apply MeasureTheory.integral_nonneg
  intro x
  simp only [Polynomial.eval_mul]
  exact mul_nonneg (mul_self_nonneg _) (by unfold gaussW; positivity)
