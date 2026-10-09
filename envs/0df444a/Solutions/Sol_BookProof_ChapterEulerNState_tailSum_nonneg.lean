-- Prove2me | solution 1 for BookProof.ChapterEulerNState.tailSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:52:00.640898+00:00
-- url     : https://prove2.me/submissions/ad1147a8-e1c0-46f5-bf3a-95b25d50467c

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.tailSum_nonneg
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (n k : ℕ) :
    0 ≤ tailSum p n k := Finset.sum_nonneg fun j _ => hp j
