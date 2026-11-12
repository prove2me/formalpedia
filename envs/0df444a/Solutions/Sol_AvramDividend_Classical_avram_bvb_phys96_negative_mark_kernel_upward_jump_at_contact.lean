-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys96_negative_mark_kernel_upward_jump_at_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:21:31.74014+00:00
-- url     : https://prove2.me/submissions/53c5b043-3cbf-44ee-921f-1c5888ceb22c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- For a reward that is zero below ruin but positive at zero, a fixed
negative jump creates a strict jump in the pre-reserve kernel.  This
boundary effect must be handled when approximating a compensator. -/
theorem solution (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 + y
    w ((1 - ε) + (-1)) - w (1 - ε) <
      w (1 + (-1)) - w 1 := by
  dsimp
  have hneg : (1 - ε : ℝ) + (-1) < 0 := by linarith
  have hpre : ¬ (1 - ε : ℝ) < 0 := by linarith
  have hzero : ¬ ((1 : ℝ) + (-1)) < 0 := by norm_num
  have hone : ¬ (1 : ℝ) < 0 := by norm_num
  simp only [if_pos hneg, if_neg hpre, if_neg hzero, if_neg hone]
  linarith
