-- Prove2me | solution 1 for BookProof.HermiteExpWall.l2_psi_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:04:41.840982+00:00
-- url     : https://prove2.me/submissions/77d81be7-7ce3-4a9b-96f9-e6e6a9f2abef

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.l2_psi_pos
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_l2_nonneg
import Theorems.Thm_BookProof_HermiteExpWall_gaussMoment_even_pos
import Theorems.Thm_BookProof_HermiteExpWall_l2_psi_sq
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) : 0 < l2 (psi N) := by

  have h := l2_psi_sq N
  have hnn : 0 ≤ l2 (psi N) := l2_nonneg _
  nlinarith [gaussMoment_even_pos N, h]
