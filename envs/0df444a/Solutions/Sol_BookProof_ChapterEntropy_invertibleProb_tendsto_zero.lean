-- Prove2me | solution 1 for BookProof.ChapterEntropy.invertibleProb_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:40:05.799928+00:00
-- url     : https://prove2.me/submissions/78091426-1889-4513-9fdd-1a6c186ea871

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.invertibleProb_tendsto_zero
import Mathlib
import Definitions.Def_ChapterEntropy
import Theorems.Thm_BookProof_ChapterEntropy_invertibleProb_eq
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution :
    Tendsto invertibleProb atTop (𝓝 0) := by

  refine tendsto_factorial_div_pow_self_atTop.congr (fun n => ?_)
  rw [invertibleProb_eq]
