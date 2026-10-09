-- Prove2me | solution 1 for BookProof.ChapterEulerNState.euler_sum_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:29.922024+00:00
-- url     : https://prove2.me/submissions/8d51ba15-32f5-4a52-a6bb-d077770651a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.euler_sum_one
import Mathlib
import Definitions.Def_ChapterEulerNState
import Theorems.Thm_BookProof_ChapterEulerNState_sum_cos_tail
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, bornProb θ n k = 1 := by

  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have hlast : bornProb θ (m + 1) m = tailProd θ m := by
    unfold bornProb; rw [if_neg (by omega), if_pos rfl]
  have hmid : ∀ k ∈ Finset.range m,
      bornProb θ (m + 1) k = tailProd θ k * Real.cos (θ k) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    unfold bornProb; rw [if_pos (by omega)]
  rw [Finset.sum_congr rfl hmid, hlast, sum_cos_tail]
  ring
