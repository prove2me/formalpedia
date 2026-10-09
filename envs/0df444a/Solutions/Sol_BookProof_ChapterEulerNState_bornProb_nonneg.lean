-- Prove2me | solution 1 for BookProof.ChapterEulerNState.bornProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:16.829114+00:00
-- url     : https://prove2.me/submissions/c47b5762-2119-4db6-b3b8-223dde70e707

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.bornProb_nonneg
import Mathlib
import Definitions.Def_ChapterEulerNState
import Theorems.Thm_BookProof_ChapterEulerNState_eulerWave_sq
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (n k : ℕ) : 0 ≤ bornProb θ n k := by

  rw [← eulerWave_sq]; exact sq_nonneg _
