-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:43:53.140861+00:00
-- url     : https://prove2.me/submissions/fc590c49-d785-43fc-8e1d-80873fcd732b

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_one
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) : RealCommutes M 1 := by

  intro m _ x; simp
