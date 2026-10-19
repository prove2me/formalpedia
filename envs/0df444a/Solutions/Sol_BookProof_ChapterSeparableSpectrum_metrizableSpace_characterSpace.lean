-- Prove2me | solution 1 for BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:48:31.018291+00:00
-- url     : https://prove2.me/submissions/c167a249-50b6-409c-b12f-5bec02268aa5

-- Generated from ChapterSeparableSpectrum.lean — solution of BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
import Theorems.Thm_BookProof_ChapterSeparableSpectrum_metrizableSpace_of_separable_continuousMap
import Theorems.Thm_BookProof_ChapterSeparableSpectrum_separableSpace_continuousMap_characterSpace
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
    MetrizableSpace (characterSpace ℂ A) := by

  haveI := separableSpace_continuousMap_characterSpace A
  exact metrizableSpace_of_separable_continuousMap _
