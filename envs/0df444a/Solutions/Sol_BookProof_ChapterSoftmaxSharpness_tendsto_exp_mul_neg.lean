-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:43.764106+00:00
-- url     : https://prove2.me/submissions/11617f4f-dceb-464a-b21a-9114bdee6fc0

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℝ) (hc : c < 0) :
    Tendsto (fun b : ℝ => Real.exp (b * c)) atTop (𝓝 0) := by

  have h : Tendsto (fun b : ℝ => b * c) atTop atBot := by
    simpa using (tendsto_id (α := ℝ)).atTop_mul_const_of_neg hc
  exact Real.tendsto_exp_atBot.comp h
