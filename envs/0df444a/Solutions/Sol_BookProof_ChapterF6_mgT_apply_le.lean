-- Prove2me | solution 1 for BookProof.ChapterF6.mgT_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:19.242136+00:00
-- url     : https://prove2.me/submissions/f5168279-57dc-4aee-b5e6-884c4cc656d7

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgT_apply_le
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mgStep_apply_le
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (s : List α) (y : α) :
    (mgT k T s) y ≤ T y + s.count y := by

  induction s using List.reverseRecOn generalizing T y with
  | nil => ?_
  | append_singleton s x ih => ?_
  · simp [ mgT ];
  · simp_all only [mgT, List.count, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.countP_append, List.countP_singleton, beq_iff_eq];
    refine le_trans ( mgStep_apply_le k _ _ _ ) ?_;
    grind
