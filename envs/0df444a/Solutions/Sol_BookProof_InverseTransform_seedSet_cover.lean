-- Prove2me | solution 1 for BookProof.InverseTransform.seedSet_cover
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:12:57.436128+00:00
-- url     : https://prove2.me/submissions/1b9a4077-c0f1-43d5-b2f3-e5de40ec3f85

-- Generated from ChapterInverseTransform.lean — solution of BookProof.InverseTransform.seedSet_cover
import Mathlib
import Definitions.Def_ChapterInverseTransform
import Theorems.Thm_BookProof_InverseTransform_cdf_zero
import Theorems.Thm_BookProof_InverseTransform_cdf_monotone
open BookProof.InverseTransform




open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

variable {n : ℕ} (p : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hp : ∀ i, 0 ≤ p i) (hsum : cdf p n = 1) :
    (⋃ k ∈ Finset.range n, seedSet p k) = Set.Ico (0 : ℝ) 1 := by

  apply Set.ext
  intro x
  constructor
  · simp only [seedSet, Set.mem_iUnion, Set.mem_Ico, Finset.mem_range]
    rintro ⟨k, hkn, hlo, hhi⟩
    refine ⟨?_, ?_⟩
    · linarith [show 0 ≤ cdf p k from Finset.sum_nonneg fun i _ => hp i]
    · have : cdf p (k + 1) ≤ cdf p n := cdf_monotone p hp (by omega)
      linarith
  · intro hx
    obtain ⟨k, hkn, hkx⟩ : ∃ k, k < n ∧ x < cdf p (k + 1) := by
      cases n with
      | zero => simp [cdf] at hsum
      | succ m => exact ⟨m, Nat.lt_succ_self m, hx.2.trans_le hsum.ge⟩
    clear hsum
    revert hkn hkx
    induction k with
    | zero =>
      intro hkn hkx
      refine Set.mem_biUnion (Finset.mem_range.mpr hkn) ?_
      simp only [seedSet, Set.mem_Ico]
      exact ⟨by simpa [cdf_zero] using hx.1, hkx⟩
    | succ k ih =>
      intro hkn hkx
      by_cases h : x < cdf p (k + 1)
      · exact ih (Nat.lt_of_succ_lt hkn) h
      · refine Set.mem_biUnion (Finset.mem_range.mpr hkn) ?_
        simp only [seedSet, Set.mem_Ico]
        exact ⟨not_lt.mp h, hkx⟩
