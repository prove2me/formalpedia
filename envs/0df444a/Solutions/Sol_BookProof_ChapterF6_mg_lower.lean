-- Prove2me | solution 1 for BookProof.ChapterF6.mg_lower
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:46.554298+00:00
-- url     : https://prove2.me/submissions/f99ad6b8-26b1-4697-913d-e76fa23792a8

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mg_lower
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mgT_le_apply_add_mgD
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (s : List α) (y : α) :
    s.count y ≤ (mg k s) y + mgD k 0 s := by

  have := mgT_le_apply_add_mgD k 0 s y
  simpa [mg] using this
