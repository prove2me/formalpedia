-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_negative_tail_real_ge_small_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:16:47.187036+00:00
-- url     : https://prove2.me/submissions/72b54d77-bdeb-4223-8147-d4c57d299f99

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_ge_small_band
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- A finite weighted jump tail preserves the small-band lower bound in real units. -/
theorem solution
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ)
    (hfinite :
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) < ⊤) :
    Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal ≤
      ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x))).toReal := by
  have hmeasure := esscher_weighted_negative_tail_ge_small_band ν φ x hφ
  have hreal := ENNReal.toReal_mono (ne_of_lt hfinite) hmeasure
  rw [ENNReal.toReal_ofReal_mul (Real.exp (-φ))
    (ν (Ioo (-1 : ℝ) (-x))) (le_of_lt (Real.exp_pos _))] at hreal
  exact hreal
