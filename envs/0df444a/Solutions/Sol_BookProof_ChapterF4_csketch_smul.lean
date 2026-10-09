-- Prove2me | solution 1 for BookProof.ChapterF4.csketch_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:01:05.38085+00:00
-- url     : https://prove2.me/submissions/9eebaca3-6ade-4d7f-90dc-643b24b957f6

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.csketch_smul
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : Fin d → Fin k) (ω : Fin d → Bool) (a : ℝ) (x : Fin d → ℝ) :
    csketch h ω (a • x) = a • csketch h ω x := by

  unfold csketch;
  ext j; simp [ mul_left_comm, Finset.mul_sum _ _ _ ] ;
