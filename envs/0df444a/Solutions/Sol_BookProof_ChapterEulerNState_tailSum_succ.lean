-- Prove2me | solution 1 for BookProof.ChapterEulerNState.tailSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:44.934327+00:00
-- url     : https://prove2.me/submissions/43aeaea1-3d87-4908-9406-07f25f21ed2d

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.tailSum_succ
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) (n k : ℕ) (h : k < n) :
    tailSum p n k = p k + tailSum p n (k + 1) := by

  rw [tailSum, tailSum, Finset.sum_eq_sum_Ico_succ_bot h]
