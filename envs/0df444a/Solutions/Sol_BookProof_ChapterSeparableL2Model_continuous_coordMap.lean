-- Prove2me | solution 1 for BookProof.ChapterSeparableL2Model.continuous_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:19:55.892698+00:00
-- url     : https://prove2.me/submissions/6640478e-f443-4b2b-bd41-5f7ead606bfb

import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterWignerSymmetry
-- Generated from ChapterSeparableL2Model.lean — theorem BookProof.ChapterSeparableL2Model.continuous_coordMap
open BookProof.ChapterWignerSymmetry
open BookProof.ChapterSeparableL2Model


noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]


theorem solution : Continuous (coordMap D) := by
  exact continuous_pi fun d => (d.1).continuous

