-- Prove2me | solution 1 for BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:57:44.786989+00:00
-- url     : https://prove2.me/submissions/3e8f09b1-1b91-45a0-bac2-372843c366c3

-- Generated from ChapterMeasureAtomicDiffuse.lean — solution of BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_countable_atomSet
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_measurableSet_atomSet
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_restrict_atomSet_add_restrict_compl
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_restrict_atomSet_eq_sum_dirac
open BookProof.ChapterMeasureAtomicDiffuse



noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure mu] :
    ∃ (A : Set α) (mua mud : Measure α), A.Countable ∧ MeasurableSet A ∧
      mu = mua + mud ∧
      mua = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α)) ∧
      mua Aᶜ = 0 ∧ NullSingletonClass mud := by

  refine ⟨atomSet mu, mu.restrict (atomSet mu), mu.restrict (atomSet mu)ᶜ,
    countable_atomSet mu, measurableSet_atomSet mu,
    (restrict_atomSet_add_restrict_compl mu).symm, restrict_atomSet_eq_sum_dirac mu, ?_,
    noAtoms_restrict_compl_atomSet mu⟩
  rw [Measure.restrict_apply (measurableSet_atomSet mu).compl]
  simp
