-- Prove2me | solution 1 for AvramDividend.Classical.esscher_indicator_l1_le_l2_sqrt_measure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:34:54.717981+00:00
-- url     : https://prove2.me/submissions/b4c8c8fd-8b66-4b07-ac06-bf65726dcf93

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (s : Set Ω)
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (s.indicator f) (1 : ℝ≥0∞) μ ≤
      eLpNorm f (2 : ℝ≥0∞) μ * (μ s) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := μ.restrict s)
    (by norm_num) hf.restrict
  rw [Measure.restrict_apply_univ] at h
  have e : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [e] at h
  exact h.trans (by gcongr; exact Measure.restrict_le_self)
