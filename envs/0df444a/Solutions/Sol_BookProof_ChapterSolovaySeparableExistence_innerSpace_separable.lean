-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.innerSpace_separable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:49:18.774654+00:00
-- url     : https://prove2.me/submissions/a1659407-2721-4a02-af64-fadee7baf403

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.innerSpace_separable
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Definitions.Def_ChapterSolovayCoordinates
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) :
    TopologicalSpace.SeparableSpace (_root_.InnerSpace N) := by

  haveI := PhysMehler.substrate_separable
  infer_instance
