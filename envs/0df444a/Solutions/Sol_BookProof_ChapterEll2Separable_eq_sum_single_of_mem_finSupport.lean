-- Prove2me | solution 1 for BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:33.361719+00:00
-- url     : https://prove2.me/submissions/06b570a8-3da6-4836-9ed5-2eef6a055133

-- Generated from ChapterEll2Separable.lean — solution of BookProof.ChapterEll2Separable.eq_sum_single_of_mem_finSupport
import Mathlib
import Definitions.Def_ChapterEll2Separable
import Theorems.Thm_BookProof_ChapterRieszFischer_riesz_fischer_hasSum
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterEll2Separable



open Filter Finset
open scoped ENNReal


open BookProof.ChapterRieszFischer

set_option maxHeartbeats 1000000 in
theorem solution (f : Ell2) {s : Finset ℕ}
    (hs : Function.support ((f : ℕ → ℝ)) ⊆ (s : Set ℕ)) :
    f = ∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i) := by

  have h₁ : HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i)) f := riesz_fischer_hasSum f
  have h₂ : HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i))
      (∑ i ∈ s, lp.single 2 i ((f : ℕ → ℝ) i)) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro i hi
    have : (f : ℕ → ℝ) i = 0 := by
      by_contra h
      exact hi (by exact_mod_cast hs h)
    simp [this]
  exact h₁.unique h₂
