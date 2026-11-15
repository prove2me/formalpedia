-- Prove2me | solution 1 for AvramDividend.Classical.counting_delta_l1_l2_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:38:39.075205+00:00
-- url     : https://prove2.me/submissions/a1b92a42-a3d5-494d-880c-47475617784a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section
theorem solution :
    ∀ n : ℕ,
      eLpNorm (({n} : Set ℕ).indicator (fun _ => (1 : ℝ))) 1
        (Measure.count : Measure ℕ) = 1 ∧
      eLpNorm (({n} : Set ℕ).indicator (fun _ => (1 : ℝ))) 2
        (Measure.count : Measure ℕ) = 1 := by
  intro n
  constructor
  · rw [eLpNorm_indicator_const (measurableSet_singleton n)
      (by norm_num) (by norm_num)]
    simp
  · rw [eLpNorm_indicator_const (measurableSet_singleton n)
      (by norm_num) (by norm_num)]
    simp
