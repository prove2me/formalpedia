-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignHom.flipVec_xor
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:19:59.307183+00:00
-- url     : https://prove2.me/submissions/6a11f270-fb71-4764-b5ea-ced78409e95a

-- Generated from ChapterFreeFieldBornSignHom.lean — solution of BookProof.ChapterFreeFieldBornSignHom.flipVec_xor
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
theorem solution (b₁ b₂ : Fin n → Bool) :
    flipVec (fun k => xor (b₁ k) (b₂ k)) = flipVec b₁ * flipVec b₂ := by

  ext k; unfold flipVec; by_cases h₁ : b₁ k <;> by_cases h₂ : b₂ k <;> simp [h₁, h₂]
