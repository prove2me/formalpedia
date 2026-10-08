-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:30:17.34243+00:00
-- url     : https://prove2.me/submissions/564da1ae-f82c-4940-9b66-56c791f58d62

-- Generated from ChapterFreeFieldBornSectionBij.lean — solution of BookProof.ChapterFreeFieldBornSectionBij.bornSection_nonneg
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_apply
open BookProof.ChapterFreeFieldBornSectionBij



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSurj


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin n → ℝ) : bornSection p ∈ nonnegOrthant n := by

  intro k; rw [bornSection_apply]; exact Real.sqrt_nonneg _
