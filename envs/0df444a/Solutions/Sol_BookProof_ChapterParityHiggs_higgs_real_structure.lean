-- Prove2me | solution 1 for BookProof.ChapterParityHiggs.higgs_real_structure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:03.208579+00:00
-- url     : https://prove2.me/submissions/3f8e35ff-7fe6-4577-a8ca-ec3613b2c27d

-- Generated from ChapterParityHiggs.lean — solution of BookProof.ChapterParityHiggs.higgs_real_structure
import Mathlib
import Definitions.Def_ChapterParityHiggs
import Theorems.Thm_BookProof_ChapterParityHiggs_realityOp_realityOp
import Theorems.Thm_BookProof_ChapterParityHiggs_higgsReal_mul_conj
import Definitions.Def_ChapterParity
open BookProof.ChapterParityHiggs



open Matrix
open scoped Kronecker
open scoped ComplexConjugate


open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 2 × Fin 2 → ℂ) :
    realityOp higgsReal (realityOp higgsReal v) = v := by

  rw [realityOp_realityOp, higgsReal_mul_conj]
  ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
