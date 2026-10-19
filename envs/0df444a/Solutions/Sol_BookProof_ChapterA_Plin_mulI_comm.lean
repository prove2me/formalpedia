-- Prove2me | solution 1 for BookProof.ChapterA.Plin_mulI_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:40.149572+00:00
-- url     : https://prove2.me/submissions/89e816e5-6aae-4695-a94b-6aaf5987f6d2

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.Plin_mulI_comm
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (S : V →L[ℝ] V) : mulI * Plin S = Plin S * mulI := by

  have h : (mulI : V →L[ℝ] V) * mulI = -1 := mulI_mul_mulI
  have e1 : (mulI : V →L[ℝ] V) * (mulI * S * mulI) = -(S * mulI) := by
    rw [← mul_assoc, ← mul_assoc, h, neg_one_mul, neg_mul]
  have e2 : (mulI * S * mulI) * (mulI : V →L[ℝ] V) = -(mulI * S) := by
    rw [mul_assoc, h, mul_neg_one]
  simp only [Plin, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, sub_mul, e1, e2, sub_neg_eq_add, sub_neg_eq_add, add_comm]
