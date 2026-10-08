-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignHom.flipVec_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:21:32.008614+00:00
-- url     : https://prove2.me/submissions/e614e10e-adf8-4d22-a2ab-b130c5a888ad

-- Generated from ChapterFreeFieldBornSignHom.lean — solution of BookProof.ChapterFreeFieldBornSignHom.flipVec_mul_self
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignHom



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignAction


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    flipVec b * flipVec b = (1 : Fin n → ℝ) := by

  ext k; unfold flipVec; by_cases h : b k <;> simp [h]
