-- Prove2me | solution 1 for BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:37.85956+00:00
-- url     : https://prove2.me/submissions/4ba9276f-979c-4227-81ed-0dea0517a0e2

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.l2_gaussPoly_le_of_gint_le
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_l2_nonneg
import Theorems.Thm_BookProof_HermiteExpWall_l2_psi_sq
import Theorems.Thm_BookProof_HermiteExpWall_l2_gaussPoly_sq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.HermiteCore
open BookProof.QgHermiteCore

noncomputable section

set_option maxHeartbeats 1000000 in

theorem solution {q : Polynomial ℝ} {K : ℝ} (hK : 0 ≤ K) (N : ℕ)
    (h : gint (q * q) ≤ K ^ 2 * gaussMoment (2 * N)) :
    l2 (gaussPoly q) ≤ K * l2 (psi N) := by
  have h1 : l2 (gaussPoly q) ^ 2 ≤ (K * l2 (psi N)) ^ 2 := by
    rw [l2_gaussPoly_sq, mul_pow, l2_psi_sq]; exact h
  have h2 : 0 ≤ l2 (gaussPoly q) := l2_nonneg _
  have h3 : 0 ≤ K * l2 (psi N) := mul_nonneg hK (l2_nonneg _)
  nlinarith
