-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_true_stopped_upper_strip_occupation_equals_physical_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:10:43.062068+00:00
-- url     : https://prove2.me/submissions/3c925c40-f579-4e8e-9810-5b2ffc23e30d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.LinearOrder
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
/-- Exact stopped Gaussian upper-strip occupation is the full horizon. -/
theorem solution
    (T n b : ℝ) (hT : 0 < T) (hTn : T ≤ n)
    (f : ℝ → ℝ) (hUpper : ∀ t : ℝ, 0 < t → t < T → b < f t) :
    (∫ t in Ioo (0 : ℝ) n,
      (if t < T ∧ b < f t then (1 : ℝ) else 0) ∂volume) = T := by
  calc
    _ = ∫ t in Ioo (0 : ℝ) n,
        (if t < T then (1 : ℝ) else 0) ∂volume := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      by_cases h : t < T
      · simp [h, hUpper t ht.1 h]
      · simp [h]
    _ = ∫ t in (Ioo (0 : ℝ) n ∩ Iio T), (1 : ℝ) ∂volume := by
      change ∫ t in Ioo (0 : ℝ) n,
          (Iio T).indicator (fun _ : ℝ => (1 : ℝ)) t ∂volume =
        ∫ t in (Ioo (0 : ℝ) n ∩ Iio T), (1 : ℝ) ∂volume
      exact setIntegral_indicator measurableSet_Iio
    _ = T := by
      rw [Ioo_inter_Iio, min_eq_right hTn]
      simp [setIntegral_const, Measure.real, Real.volume_Ioo, hT.le]
