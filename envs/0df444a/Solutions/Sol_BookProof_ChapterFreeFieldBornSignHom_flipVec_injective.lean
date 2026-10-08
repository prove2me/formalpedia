-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignHom.flipVec_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:36:40.39983+00:00
-- url     : https://prove2.me/submissions/c8130525-cd98-43e5-8dc0-5cdf80682b5c

-- Generated from ChapterFreeFieldBornSignHom.lean — solution of BookProof.ChapterFreeFieldBornSignHom.flipVec_injective
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
theorem solution : Function.Injective (flipVec : (Fin n → Bool) → (Fin n → ℝ)) := by

  intro b₁ b₂ h; ext k; replace h := congr_fun h k; simp_all [flipVec]
  grind
