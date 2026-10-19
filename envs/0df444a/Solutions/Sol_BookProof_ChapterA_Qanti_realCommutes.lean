-- Prove2me | solution 1 for BookProof.ChapterA.Qanti_realCommutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:09:01.726491+00:00
-- url     : https://prove2.me/submissions/b4c6f720-0d71-4b64-9792-e1d8040ee778

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.Qanti_realCommutes
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_realCommutes_add
import Theorems.Thm_BookProof_ChapterA_realCommutes_mul
import Theorems.Thm_BookProof_ChapterA_realCommutes_smul
import Theorems.Thm_BookProof_ChapterA_realCommutes_mulI
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S) :
    RealCommutes M (Qanti S) := by

  refine realCommutes_smul ?_ _
  exact realCommutes_add hS
    (realCommutes_mul (realCommutes_mul (realCommutes_mulI M) hS) (realCommutes_mulI M))
