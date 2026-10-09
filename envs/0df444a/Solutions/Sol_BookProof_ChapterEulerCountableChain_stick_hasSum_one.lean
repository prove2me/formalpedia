-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.stick_hasSum_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:43:47.771176+00:00
-- url     : https://prove2.me/submissions/43f2dfed-847d-4ae4-b2b2-6aeec6c961ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.stick_hasSum_one
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
import Theorems.Thm_BookProof_ChapterEulerCountableChain_stickProb_nonneg
import Theorems.Thm_BookProof_ChapterEulerCountableChain_partial_sum
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n ∧ c n ≤ 1)
    (htail : Tendsto (stickTail c) atTop (𝓝 0)) :
    HasSum (stickProb c) 1 := by

  rw [hasSum_iff_tendsto_nat_of_nonneg (stickProb_nonneg c hc) 1]
  have heq : (fun n => ∑ i ∈ Finset.range n, stickProb c i)
      = (fun n => 1 - stickTail c n) := funext (partial_sum c)
  rw [heq]
  have h0 : Tendsto (fun n => 1 - stickTail c n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub htail
  simpa using h0
