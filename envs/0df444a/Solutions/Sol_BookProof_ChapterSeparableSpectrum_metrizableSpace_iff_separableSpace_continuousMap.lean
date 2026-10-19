-- Prove2me | solution 1 for BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:54:09.815415+00:00
-- url     : https://prove2.me/submissions/c41b5035-9fcd-47e1-935b-dad0088c3180

-- Generated from ChapterSeparableSpectrum.lean — solution of BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap
import Mathlib
import Definitions.Def_ChapterSeparableSpectrum
import Theorems.Thm_BookProof_ChapterSeparableSpectrum_metrizableSpace_of_separable_continuousMap
import Theorems.Thm_BookProof_ChapterSeparableSpectrum_separableSpace_continuousMap_of_metrizable
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
theorem solution :
    MetrizableSpace Y ↔ SeparableSpace C(Y, ℂ) :=
  ⟨fun _ => separableSpace_continuousMap_of_metrizable Y,
      fun _ => metrizableSpace_of_separable_continuousMap Y⟩
