-- Prove2me | solution 1 for BookProof.ChapterEulerNState.eulerWave_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:15.826836+00:00
-- url     : https://prove2.me/submissions/a1512311-0adb-4144-9b91-69c1cd20768d

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.eulerWave_sq
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (n k : ℕ) :
    (eulerWave θ n k) ^ 2 = bornProb θ n k := by

  unfold eulerWave bornProb tailProd
  split_ifs with h1 h2
  · rw [mul_pow, ← Finset.prod_pow]
  · rw [← Finset.prod_pow]
  · ring
