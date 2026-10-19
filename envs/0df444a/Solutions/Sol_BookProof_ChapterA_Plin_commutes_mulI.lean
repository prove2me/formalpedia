-- Prove2me | solution 1 for BookProof.ChapterA.Plin_commutes_mulI
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:55.184324+00:00
-- url     : https://prove2.me/submissions/4f22667e-e943-4958-b501-2a165159560b

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.Plin_commutes_mulI
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_Plin_mulI_comm
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (S : V →L[ℝ] V) (x : V) :
    Plin S (Complex.I • x) = Complex.I • Plin S x := by

  have := congr_arg (fun T => T x) (Plin_mulI_comm S)
  simpa [ContinuousLinearMap.mul_apply] using this.symm
