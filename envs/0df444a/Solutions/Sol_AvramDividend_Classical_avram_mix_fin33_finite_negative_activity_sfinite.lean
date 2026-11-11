-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin33_finite_negative_activity_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:27.405823+00:00
-- url     : https://prove2.me/submissions/7b9427cf-271b-4ee5-8942-405d2dc54089

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (hν : ν (Iio (0 : ℝ)) ≠ ⊤) :
    SFinite (ν.restrict (Iio (0 : ℝ))) := by
  have : IsFiniteMeasure (ν.restrict (Iio (0 : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hν⟩
  infer_instance
