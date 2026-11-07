-- Prove2me | solution 1 for BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T11:40:42.006766+00:00
-- url     : https://prove2.me/submissions/0ca556fb-88a4-49b9-80e6-a409d75d0f7e

-- Generated from ChapterSolovayTailDimension.lean — solution of BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
import Mathlib
import Definitions.Def_ChapterSolovayTailDimension
import Definitions.Def_ChapterSolovay
import Theorems.Thm_BookProof_ChapterSolovayTailDimension_substrate_infinite_dimensional
import Definitions.Def_PhysMeasureBasis
open BookProof.ChapterSolovayTailDimension



noncomputable section

open MeasureTheory Set PhysMehler PhysMeasureBasis
open scoped ENNReal
open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution : ¬ FiniteDimensional ℝ _root_.InnerTail := substrate_infinite_dimensional
