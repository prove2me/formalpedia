-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignAction.boolFlip_false
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:56:17.975315+00:00
-- url     : https://prove2.me/submissions/b8633f2d-8ac7-4232-b471-5f1fc8185e51

-- Generated from ChapterFreeFieldBornSignAction.lean — solution of BookProof.ChapterFreeFieldBornSignAction.boolFlip_false
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (x : EuclideanSpace ℝ (Fin n)) :
    boolFlip (fun _ => false) x = x := by

  ext k; exact (by
  convert boolFlip_apply ( fun _ => false ) x k using 1 ; norm_num)
