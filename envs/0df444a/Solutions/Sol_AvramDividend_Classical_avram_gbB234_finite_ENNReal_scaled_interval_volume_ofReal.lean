-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB234_finite_ENNReal_scaled_interval_volume_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:27:45.894671+00:00
-- url     : https://prove2.me/submissions/7fd654be-3dc5-4a03-b8d7-29b2895773a1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (a b : ℝ) :
    B * volume (Set.Ioo a b) =
      ENNReal.ofReal (B.toReal * (b - a)) := by
  have hRe : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  calc
    B * volume (Set.Ioo a b) =
        ENNReal.ofReal B.toReal * ENNReal.ofReal (b - a) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_toReal hB]
    _ = ENNReal.ofReal (B.toReal * (b - a)) :=
      (ENNReal.ofReal_mul hRe).symm

