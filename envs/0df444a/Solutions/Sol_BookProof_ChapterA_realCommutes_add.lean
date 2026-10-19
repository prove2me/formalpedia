-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:54.244999+00:00
-- url     : https://prove2.me/submissions/8517e355-2470-4b47-86f8-e4c655fcd411

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_add
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {S T : V →L[ℝ] V}
    (hS : RealCommutes M S) (hT : RealCommutes M T) : RealCommutes M (S + T) := by

  intro m hm x
  simp only [ContinuousLinearMap.add_apply, map_add, hS m hm x, hT m hm x]
