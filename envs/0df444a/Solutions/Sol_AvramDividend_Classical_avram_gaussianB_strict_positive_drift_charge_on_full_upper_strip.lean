-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_strict_positive_drift_charge_on_full_upper_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:01:09.254042+00:00
-- url     : https://prove2.me/submissions/943a036f-8171-4f4f-b990-f8793ff5093f

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
/-- Positive Gaussian drift contributes the missing occupation charge. -/
theorem solution
    (c T b : ℝ) (hc : 0 < c) (hT : 0 < T)
    (y : ℝ → ℝ)
    (hUpper : ∀ t : ℝ, 0 < t → t < T → b < y t) :
    0 < c * ∫ t in Set.Ioo (0 : ℝ) T,
      (if b < y t then (1 : ℝ) else 0) ∂volume := by
  have hOcc :
      (∫ t in Set.Ioo (0 : ℝ) T,
        (if b < y t then (1 : ℝ) else 0) ∂volume) = T := by
    calc
      _ = ∫ _t in Set.Ioo (0 : ℝ) T, (1 : ℝ) ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        simp [hUpper t ht.1 ht.2]
      _ = T := by
        simp [setIntegral_const, Measure.real, Real.volume_Ioo, hT.le]
  rw [hOcc]
  exact mul_pos hc hT
