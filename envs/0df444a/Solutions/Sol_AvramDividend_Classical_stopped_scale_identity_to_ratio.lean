-- Prove2me | solution 1 for AvramDividend.Classical.stopped_scale_identity_to_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:33:08.110994+00:00
-- url     : https://prove2.me/submissions/c6952163-ab02-4b87-8739-4c13b0e74f44

import Mathlib.Data.ENNReal.Inv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution
    (L : ℝ≥0∞) (vx va : ℝ)
    (hL : L * ENNReal.ofReal va = ENNReal.ofReal vx)
    (hva : 0 < va) :
    L = ENNReal.ofReal (vx / va) := by
  have h_ofreal_pos : 0 < ENNReal.ofReal va := ENNReal.ofReal_pos.mpr hva
  have hne0 : ENNReal.ofReal va ≠ 0 := ne_of_gt h_ofreal_pos
  have hnetop : ENNReal.ofReal va ≠ ⊤ := ENNReal.ofReal_ne_top
  calc L = L * ENNReal.ofReal va / ENNReal.ofReal va :=
        (ENNReal.mul_div_cancel_right hne0 hnetop).symm
    _ = ENNReal.ofReal vx / ENNReal.ofReal va := by rw [hL]
    _ = ENNReal.ofReal (vx / va) := (ENNReal.ofReal_div_of_pos hva).symm
