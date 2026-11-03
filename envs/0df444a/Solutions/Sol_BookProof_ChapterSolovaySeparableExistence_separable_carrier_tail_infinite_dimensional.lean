-- Prove2me | solution 1 for BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-02T13:25:09.449298+00:00
-- url     : https://prove2.me/submissions/40d86d6e-a8a0-4e06-8a8a-fab8f104169f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSolovaySeparableExistence.lean — solution of BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_tail_infinite_dimensional
import Definitions.Def_ChapterSolovayCoordinates
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovaySeparableExistence



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ FiniteDimensional ℝ _root_.InnerTail := BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
