-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_source_HJB_strict_cap_band_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:30:57.98091+00:00
-- url     : https://prove2.me/submissions/35e1b86c-8c2a-49f6-ae70-a6ec908e70fb

import Mathlib
open Set Topology
open scoped ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(C : ℝ≥0∞) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
(hbC : ENNReal.ofReal b < C) :
IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
  Set.Icc (a / 2) b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  have hU : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} =
      Ioi (0 : ℝ) ∩ (ENNReal.ofReal ⁻¹' Iio C) := by
    ext y
    simp
  constructor
  · rw [hU]
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  · intro y hy
    constructor
    · linarith [hy.1, ha]
    · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hy.2) hbC
