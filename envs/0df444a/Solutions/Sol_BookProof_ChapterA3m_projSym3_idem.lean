-- Prove2me | solution 1 for BookProof.ChapterA3m.projSym3_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:48:07.842846+00:00
-- url     : https://prove2.me/submissions/53fd3cf1-9b82-47d4-afb6-b44e495534fe

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.projSym3_idem
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap12_sq
import Theorems.Thm_BookProof_ChapterA3m_swap23_sq
import Theorems.Thm_BookProof_ChapterA3m_braid_left
import Theorems.Thm_BookProof_ChapterA3m_braid_rel
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution : projSym3 * projSym3 = projSym3 := by

  unfold projSym3;
  -- Expand the product using the distributive property.
  simp only [smul_add, Matrix.mul_add, Algebra.mul_smul_comm, mul_one, Matrix.add_mul,
      Algebra.smul_mul_assoc, one_mul, Matrix.mul_assoc] at *;
  rw [ show swap13 = swap12 * swap23 * swap12 from braid_left.symm ];
  simp_all only [mul_assoc, swap12_sq, mul_one, swap23_sq];
  simp_all only [← mul_assoc, braid_rel, swap12_sq, one_mul, swap23_sq, mul_one];
  rw [ show swap23 * swap12 * swap23 * swap23 = swap23 * swap12 by
        rw [ mul_assoc, swap23_sq, mul_one ] ]
  rw [ show swap12 * swap23 * swap23 = swap12 by
        rw [ mul_assoc, swap23_sq, mul_one ] ]
  abel_nf
  norm_num [ ← smul_assoc ]
