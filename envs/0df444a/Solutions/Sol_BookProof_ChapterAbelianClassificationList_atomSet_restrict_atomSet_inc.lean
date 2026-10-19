-- Prove2me | solution 1 for BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:40:01.656242+00:00
-- url     : https://prove2.me/submissions/9a74c3df-711a-4ae4-ac99-87348fdb28da

-- Generated from ChapterAbelianClassificationList.lean — solution of BookProof.ChapterAbelianClassificationList.atomSet_restrict_atomSet_inc
import Mathlib
import Definitions.Def_ChapterAbelianClassificationList
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_mem_atomSet_iff
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
    atomSet (mu.restrict (atomSet mu)) = atomSet mu := by

  ext x
  simp only [mem_atomSet_iff, Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ atomSet mu
  · have hxx : ({x} : Set α) ∩ atomSet mu = {x} :=
      Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hx)
    simp [hxx, hx] at *
  · have h0 : mu {x} = 0 := by simpa [atomSet] using hx
    have hzero : mu ({x} ∩ atomSet mu) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    rw [hzero]
    simp [h0]
