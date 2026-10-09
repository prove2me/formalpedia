-- Prove2me | solution 1 for BookProof.ChapterE4.wave_succ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:31:36.887644+00:00
-- url     : https://prove2.me/submissions/67191545-f2f0-4a27-8bb3-361ea67b6732

-- Generated from ChapterE4.lean — solution of BookProof.ChapterE4.wave_succ
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (s d : ℕ) (i : ℕ) :
    wave θ s (d + 1) i =
      Real.cos (θ s) * basisVec s i + Real.sin (θ s) * wave θ (s + 1) d i := rfl
