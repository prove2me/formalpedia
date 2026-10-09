-- Prove2me | solution 1 for BookProof.ChapterEntropy.invertibleProb_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:40:04.794386+00:00
-- url     : https://prove2.me/submissions/857252c8-1749-4c76-ba7f-c9a28a2e28d0

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.invertibleProb_le_one
import Mathlib
import Definitions.Def_ChapterEntropy
import Theorems.Thm_BookProof_ChapterEntropy_invertibleProb_eq
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : invertibleProb n ≤ 1 := by

  rw [invertibleProb_eq]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le_pow n
