-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.euler_tsum_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:44:52.673039+00:00
-- url     : https://prove2.me/submissions/7f7f02ab-d9b1-43f4-9e49-d8ff1103e147
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.euler_tsum_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
import Theorems.Thm_BookProof_ChapterEulerCountableChain_stick_tsum_one
import Theorems.Thm_BookProof_ChapterEulerCountableChain_condCos_mem
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ)
    (htail : Tendsto (stickTail (condCos θ)) atTop (𝓝 0)) :
    ∑' n, stickProb (condCos θ) n = 1 := stick_tsum_one (condCos θ) (condCos_mem θ) htail
