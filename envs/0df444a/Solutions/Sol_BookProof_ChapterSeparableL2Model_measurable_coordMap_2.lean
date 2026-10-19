-- Prove2me | solution 2 for BookProof.ChapterSeparableL2Model.measurable_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:20:02.792881+00:00
-- url     : https://prove2.me/submissions/977b6a02-cd13-4147-9145-d0bc574e368e

import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStandardBorelClassification
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterWignerSymmetry
-- Generated from ChapterSeparableL2Model.lean — theorem BookProof.ChapterSeparableL2Model.measurable_coordMap
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


theorem solution : Measurable (coordMap D) := by
  exact measurable_pi_lambda _ fun d => (d.1).continuous.measurable

