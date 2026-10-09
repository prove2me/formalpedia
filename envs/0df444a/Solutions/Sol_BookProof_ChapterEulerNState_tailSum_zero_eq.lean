-- Prove2me | solution 1 for BookProof.ChapterEulerNState.tailSum_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:31.913449+00:00
-- url     : https://prove2.me/submissions/5886ba3a-2bcf-4b80-860f-85b28aea17f0

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.tailSum_zero_eq
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) (n : ℕ) :
    tailSum p n 0 = ∑ j ∈ Finset.range n, p j := by

  rw [tailSum, Finset.range_eq_Ico]
