-- Prove2me | solution 1 for BookProof.ChapterF6.mgStep_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:17.140795+00:00
-- url     : https://prove2.me/submissions/cce79a01-afec-4f54-be1e-e6b93b75dc7f

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgStep_apply_le
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (x y : α) :
    (mgStep k T x) y ≤ T y + (if y = x then 1 else 0) := by

  unfold mgStep;
  split_ifs <;> simp_all [ Finsupp.mapRange_apply ]
