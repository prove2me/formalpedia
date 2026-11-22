-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_positive_clock_integral_indicator_const_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:28:30.374809+00:00
-- url     : https://prove2.me/submissions/83f66608-ae22-4b2f-bc39-add0a0b3f388

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_positive_time_pushforward_clock_mass_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (T : ℝ≥0) (K : ℝ) :
    (∫ t : ℝ≥0, (if t ∈ Ioc (0 : ℝ≥0) T then K else 0)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal)) = (T : ℝ) * K  := by
  classical
  let μT : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  have hMass : μT (Ioc (0 : ℝ≥0) T) = (T : ℝ≥0∞) :=
    avram_twoagentA_public_positive_time_pushforward_clock_mass_20261122 T
  change (∫ t : ℝ≥0, (if t ∈ Ioc (0 : ℝ≥0) T then K else 0) ∂μT) =
    (T : ℝ) * K
  have hEq :
      (fun t : ℝ≥0 => if t ∈ Ioc (0 : ℝ≥0) T then K else 0) =
        (Ioc (0 : ℝ≥0) T).indicator (fun _ => K) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ≥0) T <;> simp [Set.indicator, ht]
  rw [hEq, MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [MeasureTheory.integral_const]
  simp [Measure.real, hMass]
