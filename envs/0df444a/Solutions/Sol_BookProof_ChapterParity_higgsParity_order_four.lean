-- Prove2me | solution 1 for BookProof.ChapterParity.higgsParity_order_four
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:35.747284+00:00
-- url     : https://prove2.me/submissions/d68c2ff9-9231-4ba1-99b0-bbc0e5999567

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.higgsParity_order_four
import Mathlib
import Definitions.Def_ChapterParity
import Theorems.Thm_BookProof_ChapterParity_higgsParity_sq
import Theorems.Thm_BookProof_ChapterParity_higgsParity_pow_four
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate

variable {n : Type*}

set_option maxHeartbeats 1000000 in
theorem solution :
    higgsParity * higgsParity ≠ 1 ∧
      higgsParity * higgsParity * (higgsParity * higgsParity) = 1 := by

  refine ⟨?_, higgsParity_pow_four⟩
  rw [higgsParity_sq]
  intro h
  have := congrArg (fun M => M 0 0) h
  norm_num [Matrix.one_apply] at this
