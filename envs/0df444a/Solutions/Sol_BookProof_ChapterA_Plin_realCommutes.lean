-- Prove2me | solution 1 for BookProof.ChapterA.Plin_realCommutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:47.0312+00:00
-- url     : https://prove2.me/submissions/88576355-8434-48f1-bcb1-463006c29033

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.Plin_realCommutes
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_realCommutes_add
import Theorems.Thm_BookProof_ChapterA_realCommutes_mul
import Theorems.Thm_BookProof_ChapterA_realCommutes_smul
import Theorems.Thm_BookProof_ChapterA_realCommutes_neg
import Theorems.Thm_BookProof_ChapterA_realCommutes_mulI
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {S : V →L[ℝ] V} (hS : RealCommutes M S) :
    RealCommutes M (Plin S) := by

  refine realCommutes_smul ?_ _
  rw [sub_eq_add_neg]
  exact realCommutes_add hS
    (realCommutes_neg
      (realCommutes_mul (realCommutes_mul (realCommutes_mulI M) hS) (realCommutes_mulI M)))
