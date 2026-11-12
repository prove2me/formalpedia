-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB70_uniform_two_grid_weighted_block_regroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:11:46.397201+00:00
-- url     : https://prove2.me/submissions/f8f6521f-7e63-4f61-85a3-867e84cad753

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb85_uniform_weighted_block_regroup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators

theorem solution (m p : ℕ) (f g : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      g i * (Finset.range (p + 1)).sum (fun j =>
        f (i * (p + 1) + j))) =
    (Finset.range ((m + 1) * (p + 1))).sum (fun r =>
      g (r / (p + 1)) * f r) := by
  simpa using (avram_gb85_uniform_weighted_block_regroup
    m (p + 1) (by omega) f g).symm
