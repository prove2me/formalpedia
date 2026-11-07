-- Prove2me | solution 1 for BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T12:27:21.909732+00:00
-- url     : https://prove2.me/submissions/1b312018-dccd-465e-a72d-34f6baff35e2

-- Generated from ChapterSeparableL2Model.lean — solution of BookProof.ChapterSeparableL2Model.separableSpace_of_linearIsometry
import Mathlib
import Definitions.Def_ChapterSeparableL2Model
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianCyclicModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterStandardBorelClassification
open BookProof.ChapterSeparableL2Model



universe u

noncomputable section

open MeasureTheory TopologicalSpace


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianCyclicModel
open BookProof.ChapterAbelianDirectSum BookProof.ChapterLinftyMultiplication
open BookProof.ChapterStandardBorelClassification

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsFiniteMeasure mu] [mu.WeaklyRegular]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] (D : Set C(Y, ℂ)) [Countable D]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] (mu : Measure Y) [IsProbabilityMeasure mu] [mu.WeaklyRegular]
variable {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in

theorem solution [SeparableSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (V : E →ₗᵢ[ℂ] H) : SeparableSpace E := by
  haveI : SecondCountableTopology H := UniformSpace.secondCountable_of_separable H
  haveI := (V.isometry.isEmbedding).secondCountableTopology
  infer_instance
