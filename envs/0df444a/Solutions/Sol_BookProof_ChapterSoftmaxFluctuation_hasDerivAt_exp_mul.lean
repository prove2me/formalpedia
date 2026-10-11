-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:44.167908+00:00
-- url     : https://prove2.me/submissions/41a374bb-2790-4bbe-8712-32dbd691451b

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.hasDerivAt_exp_mul
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta c : ℝ) :
    HasDerivAt (fun b : ℝ => Real.exp (b * c)) (c * Real.exp (beta * c)) beta := by

  have h : HasDerivAt (fun b : ℝ => b * c) c beta := by
    simpa using (hasDerivAt_id beta).mul_const c
  simpa [mul_comm] using h.exp
