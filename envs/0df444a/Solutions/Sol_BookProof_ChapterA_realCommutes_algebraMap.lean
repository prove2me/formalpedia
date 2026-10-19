-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:44.629199+00:00
-- url     : https://prove2.me/submissions/47cb6885-afc2-4ec9-a81c-6a61f00a7e67

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_algebraMap
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_realCommutes_one
import Theorems.Thm_BookProof_ChapterA_realCommutes_smul
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (r : ℝ) :
    RealCommutes M (algebraMap ℝ (V →L[ℝ] V) r) := by

  rw [Algebra.algebraMap_eq_smul_one]
  exact realCommutes_smul (realCommutes_one M) r
