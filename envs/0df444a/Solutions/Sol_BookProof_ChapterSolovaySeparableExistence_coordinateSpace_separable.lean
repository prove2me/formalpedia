-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.coordinateSpace_separable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:49:00.655115+00:00
-- url     : https://prove2.me/submissions/e4bf3474-f8f3-44bf-99c8-e62e081cae01

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.coordinateSpace_separable
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Definitions.Def_ChapterSolovayCoordinates
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) :
    TopologicalSpace.SeparableSpace (CoordinateSpace N) := by

  infer_instance
