-- Prove2me | solution 1 for BookProof.ChapterParity.fermionParity_order_four
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:51.201521+00:00
-- url     : https://prove2.me/submissions/d4c6cab3-815b-4fb0-b8b4-82ca54209663

-- Generated from ChapterParity.lean — solution of BookProof.ChapterParity.fermionParity_order_four
import Mathlib
import Definitions.Def_ChapterParity
import Theorems.Thm_BookProof_ChapterParity_mgamma0_sq
import Definitions.Def_ChapterA3
open BookProof.ChapterParity



open Matrix
open scoped ComplexConjugate
open BookProof.ChapterA3

variable {n : Type*}

set_option maxHeartbeats 1000000 in

theorem solution :
    mgamma 0 * mgamma 0 ≠ 1 ∧
      mgamma 0 * mgamma 0 * (mgamma 0 * mgamma 0) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [mgamma0_sq]
    intro h
    have := congrArg (fun M => M 0 0) h
    norm_num [Matrix.one_apply] at this
  · rw [mgamma0_sq]; simp
