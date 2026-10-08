-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:57:10.818862+00:00
-- url     : https://prove2.me/submissions/646edb83-0eea-473a-b838-9c4f601ab96d

-- Generated from ChapterFreeFieldBornSignAction.lean — solution of BookProof.ChapterFreeFieldBornSignAction.boolFlip_comp
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b₁ b₂ : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    boolFlip b₁ (boolFlip b₂ x) = boolFlip (fun k => xor (b₁ k) (b₂ k)) x := by

  ext k; simp only [boolFlip_apply]
  cases h₁ : b₁ k <;> cases h₂ : b₂ k <;> simp_all
