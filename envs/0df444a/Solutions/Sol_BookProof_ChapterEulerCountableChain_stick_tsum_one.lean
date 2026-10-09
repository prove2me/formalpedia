-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stick_tsum_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:44:36.370729+00:00
-- url     : https://prove2.me/submissions/efe908db-14df-4368-9720-ea6e99de8d48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stick_tsum_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
import Theorems.Thm_BookProof_ChapterEulerCountableChain_stick_hasSum_one
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1)
    (htail : Tendsto (stickTail c) atTop (𝓝 0)) :
    ∑' n, stickProb c n = 1 := (stick_hasSum_one c hc htail).tsum_eq
