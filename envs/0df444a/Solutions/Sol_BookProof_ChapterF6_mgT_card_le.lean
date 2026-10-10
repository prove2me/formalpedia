-- Prove2me | solution 1 for BookProof.ChapterF6.mgT_card_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:02:35.941981+00:00
-- url     : https://prove2.me/submissions/7d4ca908-7623-4f1e-9422-efc06180c0cc

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mgT_card_le
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mgT_cons
import Theorems.Thm_BookProof_ChapterF6_mgStep_card_le
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]


@[simp] private theorem mgT_nil (k : ℕ) (T : α →₀ ℕ) : mgT k T [] = T := rfl

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (T : α →₀ ℕ) (s : List α) (hT : T.support.card ≤ k) :
    (mgT k T s).support.card ≤ k := by

  induction s generalizing T with
  | nil => ?_
  | cons x s ih => ?_
  all_goals simp_all only [mgT_nil, mgT_cons]
  exact ih _ ( mgStep_card_le k T x hT )
