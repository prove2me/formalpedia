-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB177_real_symmetric_interval_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:41:18.323894+00:00
-- url     : https://prove2.me/submissions/aa39563b-4f8f-4445-aa1d-e1755b4fa88d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution (y ε : ℝ) :
    volume (Ioo (y - ε) (y + ε)) =
      ENNReal.ofReal (2 * ε) := by
  rw [Real.volume_Ioo]
  congr 1
  ring
