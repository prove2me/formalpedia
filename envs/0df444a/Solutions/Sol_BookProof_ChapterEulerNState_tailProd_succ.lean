-- Prove2me | solution 1 for BookProof.ChapterEulerNState.tailProd_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:50:50.1025+00:00
-- url     : https://prove2.me/submissions/a2fe0020-d611-4afa-832a-548a3a614784

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.tailProd_succ
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (m : ℕ) :
    tailProd θ (m + 1) = tailProd θ m * Real.sin (θ m) ^ 2 := by

  simp [tailProd, Finset.prod_range_succ]
