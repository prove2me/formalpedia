-- Prove2me | solution 1 for BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:48:27.72618+00:00
-- url     : https://prove2.me/submissions/d7a462bd-b288-42ee-b0a0-09b10db313f6

-- Generated from ChapterSeparableSpectrum.lean — solution of BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
open BookProof.ChapterSeparableSpectrum



noncomputable section

open MeasureTheory TopologicalSpace WeakDual


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum
open BookProof.ChapterStandardBorelClassification

variable (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]

set_option maxHeartbeats 1000000 in
theorem solution [MetrizableSpace Y] :
    SeparableSpace C(Y, ℂ) := by

  letI := metrizableSpaceMetric Y
  haveI : SecondCountableTopology Y := UniformSpace.secondCountable_of_separable Y
  infer_instance
