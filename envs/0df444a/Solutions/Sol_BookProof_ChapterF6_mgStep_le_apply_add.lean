-- Prove2me | solution 1 for BookProof.ChapterF6.mgStep_le_apply_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:18.1061+00:00
-- url     : https://prove2.me/submissions/2d88964b-c87d-4be8-a347-2090a892b390

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgStep_le_apply_add
import Mathlib
import Definitions.Def_ChapterF6
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (x y : α) :
    T y + (if y = x then 1 else 0)
      ≤ (mgStep k T x) y + (if 0 < T x ∨ T.support.card < k then 0 else 1) := by

  unfold mgStep; split_ifs <;> simp_all [ Finsupp.mapRange_apply ] ;
  omega
