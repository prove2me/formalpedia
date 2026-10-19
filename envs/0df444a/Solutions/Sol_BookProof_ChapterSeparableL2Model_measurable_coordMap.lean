-- Prove2me | solution 1 for BookProof.ChapterSeparableL2Model.measurable_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:43:25.012099+00:00
-- url     : https://prove2.me/submissions/92cddabc-9893-4091-8e07-6f60c5c2e1f3

-- Generated from ChapterSeparableL2Model.lean — solution of BookProof.ChapterSeparableL2Model.measurable_coordMap
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Theorems.Thm_BookProof_ChapterSeparableL2Model_continuous_coordMap
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStandardBorelClassification
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterSeparableL2Model



noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification
open BookProof.ChapterWignerSymmetry

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]

set_option maxHeartbeats 1000000 in
theorem solution : Measurable (coordMap D) := (continuous_coordMap D).measurable
