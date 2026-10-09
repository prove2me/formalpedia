-- Prove2me | solution 1 for BookProof.ChapterEulerCountableChain.one_sub_condCos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:44:50.610044+00:00
-- url     : https://prove2.me/submissions/9e55f43f-b1b4-4b32-b807-df71d087d0fa

-- Generated from ChapterEulerCountableChain.lean — solution of BookProof.ChapterEulerCountableChain.one_sub_condCos
import Mathlib
import Definitions.Def_ChapterEulerCountableChain
open BookProof.ChapterEulerCountableChain



open scoped BigOperators
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (n : ℕ) :
    1 - condCos θ n = Real.sin (θ n) ^ 2 := by

  rw [condCos]
  nlinarith [Real.sin_sq_add_cos_sq (θ n)]
