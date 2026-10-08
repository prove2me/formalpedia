-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSignAction.bornMap_boolFlip
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:56:40.670961+00:00
-- url     : https://prove2.me/submissions/a6aa3197-b8ff-48f9-add3-995f5089c079

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignAction

variable {n : ℕ}

open MeasureTheory BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge BookProof.ChapterFreeFieldBornSignAction in
theorem solution (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    bornMap (boolFlip b x) = bornMap x := by
  funext k
  simp only [bornMap, boolFlip_apply]
  split <;> ring
