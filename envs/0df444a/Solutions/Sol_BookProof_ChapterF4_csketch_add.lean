-- Prove2me | solution 1 for BookProof.ChapterF4.csketch_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:00:52.292675+00:00
-- url     : https://prove2.me/submissions/a5d4c952-a3e9-4c21-932b-70d9cb5130c4

-- Generated from ChapterF4.lean — solution of BookProof.ChapterF4.csketch_add
import Mathlib
import Definitions.Def_ChapterF4
open BookProof.ChapterF4



open scoped BigOperators Matrix

variable {d k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : Fin d → Fin k) (ω : Fin d → Bool) (x y : Fin d → ℝ) :
    csketch h ω (x + y) = csketch h ω x + csketch h ω y := by

  ext j; exact (by
  unfold csketch; simp [ mul_add ] ;
  simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun _ _ =>
      by split_ifs <;> ring;);
