-- Prove2me | solution 1 for BookProof.ChapterEll2Separable.sum_single_rat_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:34:18.637431+00:00
-- url     : https://prove2.me/submissions/fbcadbb5-b8ef-40db-b3ec-5b46e2957fcc

-- Generated from ChapterEll2Separable.lean — solution of BookProof.ChapterEll2Separable.sum_single_rat_mem_range
import Mathlib
import Definitions.Def_ChapterEll2Separable
open BookProof.ChapterEll2Separable



open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution (s : Finset ℕ) (q : ℕ → ℚ) :
    (∑ i ∈ s, lp.single 2 i ((q i : ℝ))) ∈ Set.range ratVec := by

  classical
  set q' : ℕ → ℚ := fun i => if i ∈ s then q i else 0 with hq'
  refine ⟨Finsupp.onFinset s q' ?_, ?_⟩
  · intro a ha
    by_contra has
    exact ha (by simp [hq', has])
  · have hsub : (Finsupp.onFinset s q' (by
        intro a ha
        by_contra has
        exact ha (by simp [hq', has]))).support ⊆ s := Finsupp.support_onFinset_subset
    rw [ratVec]
    rw [Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [Finsupp.onFinset_apply, hq', hi]
    · intro i _ hi
      have : q' i = 0 := by
        by_contra h
        exact hi (Finsupp.mem_support_iff.2 (by simpa [Finsupp.onFinset_apply] using h))
      simp [Finsupp.onFinset_apply, this]
