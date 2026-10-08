-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignGauge.bornMap_signFlip
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:19:49.875983+00:00
-- url     : https://prove2.me/submissions/9039df33-ee6d-45d0-b961-ce2cd62d831d

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge

variable {n : ℕ}

open MeasureTheory BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge in
theorem solution {s : Fin n → ℝ} (hs : ∀ k, s k = 1 ∨ s k = -1)
    (x : EuclideanSpace ℝ (Fin n)) :
    bornMap (signFlip s x) = bornMap x := by
  funext k
  simp only [bornMap, signFlip_apply]
  rcases hs k with h | h <;> rw [h] <;> ring
