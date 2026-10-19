-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:45:48.646662+00:00
-- url     : https://prove2.me/submissions/331bde00-f012-41bc-addf-64aedab3ed8a

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_smul
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S)
    (r : ℝ) : RealCommutes M (r • S) := by

  intro m hm x
  simp only [ContinuousLinearMap.smul_apply]
  rw [hS m hm x]
  exact (ContinuousLinearMap.map_smul_of_tower m r (S x)).symm
