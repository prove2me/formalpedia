-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:03:11.224897+00:00
-- url     : https://prove2.me/submissions/f4c092a1-4fdc-48b5-9c36-45d14ba034b5

-- Generated from ChapterFreeFieldBornSignGauge.lean — theorem BookProof.ChapterFreeFieldBornSignGauge.signFlip_neg_one
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignGauge

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn

theorem solution (x : EuclideanSpace ℝ (Fin n)) :
    signFlip (fun _ => -1) x = -x := by
  ext k
  change (-1 : ℝ) * x k = -(x k)
  simp


#print axioms solution
