-- Prove2me | solution 1 for BookProof.ChapterF6.mg_upper
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:05:32.072976+00:00
-- url     : https://prove2.me/submissions/5b76489a-adb5-4a30-bfc4-a7f8050dcb04

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.mg_upper
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mgT_apply_le
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (s : List α) (y : α) : (mg k s) y ≤ s.count y := by

  have := mgT_apply_le k 0 s y
  simpa [mg] using this
