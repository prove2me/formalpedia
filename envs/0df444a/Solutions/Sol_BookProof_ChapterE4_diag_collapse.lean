-- Prove2me | solution 1 for BookProof.ChapterE4.diag_collapse
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:32:19.376989+00:00
-- url     : https://prove2.me/submissions/b1e528a7-7926-4489-ad48-a20c3178b43d

-- Generated from ChapterE4.lean — solution of BookProof.ChapterE4.diag_collapse
import Mathlib
import Definitions.Def_ChapterE4
import Theorems.Thm_BookProof_ChapterE4_wave_succ
import Theorems.Thm_BookProof_ChapterE4_cross_diag_zero
open BookProof.ChapterE4



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (s d i : ℕ) :
    (wave θ s (d + 1) i) ^ 2
      = Real.cos (θ s) ^ 2 * (basisVec s i) ^ 2
        + Real.sin (θ s) ^ 2 * (wave θ (s + 1) d i) ^ 2 := by

  grind +suggestions
