-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:55.838492+00:00
-- url     : https://prove2.me/submissions/732de071-f102-4e46-af06-8a38cf394be5

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_mul
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {S T : V →L[ℝ] V}
    (hS : RealCommutes M S) (hT : RealCommutes M T) : RealCommutes M (S * T) := by

  intro m hm x
  simp only [ContinuousLinearMap.mul_apply]
  rw [hT m hm x, hS m hm (T x)]
