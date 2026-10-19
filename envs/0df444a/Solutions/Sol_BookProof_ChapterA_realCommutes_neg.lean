-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:45:49.762091+00:00
-- url     : https://prove2.me/submissions/337e0b38-30c7-4acd-a73e-6a1bc4ea2f2a

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_neg
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S) :
    RealCommutes M (-S) := by

  intro m hm x
  simp only [ContinuousLinearMap.neg_apply, map_neg, hS m hm x]
