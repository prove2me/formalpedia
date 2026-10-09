-- Prove2me | solution 1 for BookProof.ChapterE4.cond_prob_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:32:20.342989+00:00
-- url     : https://prove2.me/submissions/d4501779-86fa-43ac-87df-1c8a7edcef39

-- Generated from ChapterE4.lean — solution of BookProof.ChapterE4.cond_prob_sum
import Mathlib
import Definitions.Def_ChapterE4
open BookProof.ChapterE4



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (s : ℕ) :
    Real.cos (θ s) ^ 2 + Real.sin (θ s) ^ 2 = 1 := by

  exact Real.cos_sq_add_sin_sq _
