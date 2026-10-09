-- Prove2me | solution 1 for BookProof.ChapterEulerNState.euler_wave_unit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:30.928155+00:00
-- url     : https://prove2.me/submissions/2d1040f7-5d1f-4789-888d-a888c78652dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.euler_wave_unit
import Mathlib
import Definitions.Def_ChapterEulerNState
import Theorems.Thm_BookProof_ChapterEulerNState_eulerWave_sq
import Theorems.Thm_BookProof_ChapterEulerNState_euler_sum_one
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, (eulerWave θ n k) ^ 2 = 1 := by

  simp_rw [eulerWave_sq]; exact euler_sum_one θ hn
