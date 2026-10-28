-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_interval_restricted_volume_ne_zero_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:58:06.894026+00:00
-- url     : https://prove2.me/submissions/900cf099-5140-4d9d-acb2-c403bbd75f06

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution :
    (volume.restrict (Ioc (0 : ℝ) 1) : Measure ℝ) ≠ 0 := by
  intro hZero
  have hSetZero :
      (volume.restrict (Ioc (0 : ℝ) 1) : Measure ℝ)
        (Ioc (0 : ℝ) 1) = 0 := by
    rw [hZero]
    simp
  have hVolumeZero :
      (volume : Measure ℝ) (Ioc (0 : ℝ) 1) = 0 := by
    simpa only [Measure.restrict_apply measurableSet_Ioc,
      Set.inter_self] using hSetZero
  rw [Real.volume_Ioc] at hVolumeZero
  norm_num at hVolumeZero
