-- Prove2me | solution 1 for BookProof.ChapterParityQL.QLParity_order_four
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:21.768108+00:00
-- url     : https://prove2.me/submissions/53d73430-2592-477f-b10d-2cfc56a895ff

-- Generated from ChapterParityQL.lean — solution of BookProof.ChapterParityQL.QLParity_order_four
import Mathlib
import Definitions.Def_ChapterParityQL
import Theorems.Thm_BookProof_ChapterParityQL_QLParity_sq
import Theorems.Thm_BookProof_ChapterParityQL_QLParity_pow_four
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
open BookProof.ChapterParityQL



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution :
    QLParity * QLParity ≠ 1 ∧
      QLParity * QLParity * (QLParity * QLParity) = 1 := by

  refine ⟨?_, QLParity_pow_four⟩
  rw [QLParity_sq]
  intro h
  have := congrArg (fun M => M (0, 0) (0, 0)) h
  norm_num [Matrix.one_apply] at this
