-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_mulI
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:45:50.8879+00:00
-- url     : https://prove2.me/submissions/4a204115-c7d8-425c-b093-ca7454987eac

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_mulI
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) : RealCommutes M (mulI : V →L[ℝ] V) := by

  intro m _ x
  simp only [mulI_apply]
  rw [map_smul]
