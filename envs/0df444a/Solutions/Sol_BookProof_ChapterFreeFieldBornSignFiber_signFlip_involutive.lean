-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignFiber.signFlip_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:28:55.805193+00:00
-- url     : https://prove2.me/submissions/ee1e228d-e4d1-4af1-90f7-6bf4a223a84c

-- Generated from ChapterFreeFieldBornSignFiber.lean — solution of BookProof.ChapterFreeFieldBornSignFiber.signFlip_involutive
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignFiber
open BookProof.ChapterFreeFieldBornSignFiber



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    signFlip s (signFlip s x) = x := by

  ext k; cases hs k <;> simp [*]
