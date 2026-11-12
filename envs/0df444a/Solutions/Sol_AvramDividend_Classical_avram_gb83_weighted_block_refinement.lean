-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb83_weighted_block_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:16:06.9132+00:00
-- url     : https://prove2.me/submissions/cc03ddad-1569-47b1-8284-9f7ccb668e1c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb84_shifted_finite_difference_telescope
import Theorems.Thm_AvramDividend_Classical_avram_gb85_uniform_weighted_block_regroup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical

/-- Regroup a weighted finite-difference sum into fixed-size blocks. -/
theorem solution (m b : ℕ) (hb : 0 < b) (f g : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      g i * (f ((i + 1) * b) - f (i * b))) =
    (Finset.range ((m + 1) * b)).sum (fun r =>
      g (r / b) * (f (r + 1) - f r)) := by
  calc
    _ = (Finset.range (m + 1)).sum (fun i =>
          g i * (Finset.range b).sum (fun j =>
            f (i * b + j + 1) - f (i * b + j))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [avram_gb84_shifted_finite_difference_telescope]
          congr 1
          ring
    _ = _ := by
          simpa using
            (avram_gb85_uniform_weighted_block_regroup m b hb
              (fun r => f (r + 1) - f r) g).symm
