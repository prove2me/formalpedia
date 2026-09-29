-- Prove2me | solution 1 for BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:54:58.842173+00:00
-- url     : https://prove2.me/submissions/c77c40f0-ac3b-44ed-b8ff-42387884f943

-- Generated from ChapterSirkRestart.lean — solution of BookProof.ChapterSirkRestart.norm_pow_apply_le_of_contraction
import Mathlib
import Definitions.Def_ChapterSirkRestart
open BookProof.ChapterSirkRestart








noncomputable section

open Filter Topology


open BookProof.ChapterH6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (S : E →L[ℂ] E) (hS : ∀ w : E, ‖S w‖ ≤ ‖w‖)
    (n : ℕ) (v : E) : ‖(S ^ n) v‖ ≤ ‖v‖ := by

  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ((S ^ (n + 1)) v) = S ((S ^ n) v) := by
      rw [pow_succ']; rfl
    rw [hstep]
    exact le_trans (hS _) ih
