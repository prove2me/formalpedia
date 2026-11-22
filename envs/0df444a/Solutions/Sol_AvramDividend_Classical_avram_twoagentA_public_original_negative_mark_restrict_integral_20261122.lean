-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_negative_mark_restrict_integral_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:23:07.81499+00:00
-- url     : https://prove2.me/submissions/7fcf72f2-b328-42a6-91bf-abf41ad6e1ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    (∫ z : ℝ, (if z ∈ B then z else 0)
      ∂(ν.restrict (Iio (0 : ℝ)))) =
      (∫ z in B, z ∂ν)  := by
  classical
  calc
    (∫ z : ℝ, (if z ∈ B then z else 0)
      ∂(ν.restrict (Iio (0 : ℝ)))) =
        (∫ z in B, z ∂(ν.restrict (Iio (0 : ℝ)))) := by
          change (∫ z : ℝ, B.indicator (fun z => z) z
            ∂(ν.restrict (Iio (0 : ℝ)))) = _
          rw [MeasureTheory.integral_indicator hB]
    _ = (∫ z in B, z ∂ν) := by
      change (∫ z : ℝ, z ∂((ν.restrict (Iio (0 : ℝ))).restrict B)) =
        ∫ z : ℝ, z ∂(ν.restrict B)
      rw [Measure.restrict_restrict hB, Set.inter_eq_left.mpr hNeg]
