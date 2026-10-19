-- Prove2me | solution 1 for BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:48:29.873828+00:00
-- url     : https://prove2.me/submissions/67ab291c-2303-4ab7-8117-e19c68884fae

-- Generated from ChapterSeparableSpectrum.lean — solution of BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_characterSpace
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
import Theorems.Thm_BookProof_ChapterAbelianGelfandModel_gelfandModel_isometry
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterStandardBorelClassification
open BookProof.ChapterSeparableSpectrum



noncomputable section

open MeasureTheory TopologicalSpace WeakDual


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum
open BookProof.ChapterStandardBorelClassification

variable (Y : Type*) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [SeparableSpace C(Y, ℂ)] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : Type*) [CommCStarAlgebra A]

set_option maxHeartbeats 1000000 in
theorem solution [SeparableSpace A] :
    SeparableSpace C(characterSpace ℂ A, ℂ) :=
  ((gelfandModel A).surjective.denseRange).separableSpace
      (gelfandModel_isometry A).continuous
