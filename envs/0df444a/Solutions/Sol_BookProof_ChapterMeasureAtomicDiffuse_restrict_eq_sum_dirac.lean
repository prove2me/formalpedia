-- Prove2me | solution 1 for BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:57:16.228476+00:00
-- url     : https://prove2.me/submissions/374bb24c-f584-49f0-8bee-ada980d70af4

-- Generated from ChapterMeasureAtomicDiffuse.lean — solution of BookProof.ChapterMeasureAtomicDiffuse.restrict_eq_sum_dirac
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse



noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

set_option maxHeartbeats 1000000 in
theorem solution {A : Set α} (hc : A.Countable) :
    mu.restrict A = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α)) := by

  ext s hs
  rw [Measure.restrict_apply hs, Measure.sum_apply _ hs]
  have hunion : s ∩ A = ⋃ x ∈ A, ({x} ∩ s) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨hys, hyA⟩
      exact ⟨y, hyA, rfl, hys⟩
    · rintro ⟨x, hxA, rfl, hys⟩
      exact ⟨hys, hxA⟩
  rw [hunion, measure_biUnion hc (fun x _ y _ hxy => by
      simp only [Function.onFun]
      exact Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left
        (by simpa using hxy))
    (fun x _ => (measurableSet_singleton x).inter hs)]
  refine tsum_congr fun x => ?_
  by_cases hx : (x : α) ∈ s
  · simp [hx, Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hx)]
  · have hempty : ({(x : α)} : Set α) ∩ s = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl
      exact hx
    simp [hx, hempty]
