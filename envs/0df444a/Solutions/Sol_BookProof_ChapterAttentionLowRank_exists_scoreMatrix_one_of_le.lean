-- Prove2me | solution 1 for BookProof.ChapterAttentionLowRank.exists_scoreMatrix_one_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:43:54.321689+00:00
-- url     : https://prove2.me/submissions/fb59aff8-5ee7-406c-8a0d-4171df0e77f3

-- Generated from ChapterAttentionLowRank.lean — solution of BookProof.ChapterAttentionLowRank.exists_scoreMatrix_one_of_le
import Mathlib
import Definitions.Def_ChapterAttentionLowRank
import Theorems.Thm_BookProof_ChapterAttentionLowRank_scoreMatrix_apply
open BookProof.ChapterAttentionLowRank



open scoped BigOperators

noncomputable section


variable {m d : ℕ}

variable {m d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (hd : m ≤ d) :
    ∃ Q K : Fin m → Fin d → ℝ, scoreMatrix Q K = 1 := by

  classical
  refine ⟨fun i a => if (a : ℕ) = (i : ℕ) then 1 else 0,
    fun j a => if (a : ℕ) = (j : ℕ) then 1 else 0, ?_⟩
  ext i j
  have hi : (i : ℕ) < d := lt_of_lt_of_le i.isLt hd
  have hsum : (∑ a : Fin d, (if (a : ℕ) = (i : ℕ) then (1 : ℝ) else 0)
      * (if (a : ℕ) = (j : ℕ) then (1 : ℝ) else 0))
      = if (i : ℕ) = (j : ℕ) then 1 else 0 := by
    rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin d)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ (i : ℕ) := by
        intro h
        exact hb (Fin.ext h)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [scoreMatrix_apply, hsum, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · have : (i : ℕ) ≠ (j : ℕ) := fun hc => h (Fin.ext hc)
    simp [h, this]
