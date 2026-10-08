-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:28:22.206934+00:00
-- url     : https://prove2.me/submissions/0b00c0ed-d6db-49bd-8d68-0636ce5da485

-- Generated from ChapterFreeFieldBornSignFiber.lean — solution of BookProof.ChapterFreeFieldBornSignFiber.signFlip_comp
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignFiber
open BookProof.ChapterFreeFieldBornSignFiber



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s t : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    signFlip s (signFlip t x) = signFlip (fun k => s k * t k) x := by

  ext k; simp [signFlip_apply, mul_assoc]
