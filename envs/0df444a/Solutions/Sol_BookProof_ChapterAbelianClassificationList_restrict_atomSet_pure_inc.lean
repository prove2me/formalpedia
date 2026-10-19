-- Prove2me | solution 1 for BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:40:23.236163+00:00
-- url     : https://prove2.me/submissions/8d30e405-5051-42b6-b74b-0a93d0b43fcd

-- Generated from ChapterAbelianClassificationList.lean — solution of BookProof.ChapterAbelianClassificationList.restrict_atomSet_pure_inc
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_measurableSet_atomSet
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterAbelianClassificationList



noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure α) [IsFiniteMeasure mu] :
    (mu.restrict (atomSet mu)) (atomSet (mu.restrict (atomSet mu)))ᶜ = 0 := by

  rw [atomSet_restrict_atomSet mu,
    Measure.restrict_apply (measurableSet_atomSet mu).compl]
  simp
